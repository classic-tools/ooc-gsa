(* 	$Id: SystemFlags.Mod,v 1.33 1999/06/21 10:48:23 acken Exp $	 *)
MODULE SystemFlags;
(*  Implements parsing and storing/loading of system flags.
    Copyright (C) 1996-1999  Michael van Acken

    This file is part of OOC.

    OOC is free software; you can redistribute it and/or modify it
    under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.  

    OOC is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
    License for more details. 

    You should have received a copy of the GNU General Public License
    along with OOC. If not, write to the Free Software Foundation, 59
    Temple Place - Suite 330, Boston, MA 02111-1307, USA.
*)
(* This module implements the mechanisms described in doc/ExternalC.  *)

IMPORT
  Strings, BinaryRider,
  E := Error, S := Scanner, D := Data, Sym := SymbolTable, StdTypes, 
  StdPragmas, External;
  

TYPE 
  Modifier = RECORD
    name: ARRAY 20 OF CHAR;              (* modifier name *)
    objId: SET;                          (* objects where it can be set *)
    objFlag: SHORTINT;                   (* index set in Object.flags *)
    structId: SET;                       (* types where it can be set *)
    structFlag: SHORTINT;                (* index set in Struct.flags *)
  END;

CONST
  strOffset = D.strPointer;
  offsetBE = MAX(SET)+1;
  objOpenArrayParam = 31;
  objReferenceParam = 30;
  objVarRecordParam = 29;
  objStructValueParam = 28;
  
VAR
  mods: ARRAY 17 OF Modifier;
  emptyString: ARRAY 2 OF CHAR;
  

CONST  (* valid values for variable `mode' *)
  normal = 0;                            (* standard Oberon-2 source file *)
  foreign = 1;                           (* foreign module *)
  interface = 2;                         (* interface module *)

CONST  (* list of calling conventions; quite short, really *)
  callConvC* = 0;                        (* C, caller removes arguments *)
  callConvPascal* = 1;                   (* Pascal, callee removes arguments *)
  callConvFortran* = 2;                  (* FORTRAN, not supported *)
  callConvModula2* = 3;                  (* Modula-2, not supported *)
  
VAR
  mode: SHORTINT;
  (* module mode; one from {normal, foreign, interface} *)
  callConv: INTEGER;
  (* calling convention specified in header of an INTERFACE or FOREIGN 
     module *)
  noLibFileRead*: BOOLEAN;
  (* iff TRUE procedure ReadObjectInfo will not try to load the library 
     summary information of O2 libraries appearing in symbol files *)
  

TYPE  
  (* back-end dependent information installed in Data.Object and Data.Struct 
     blocks in the symbol table (in field Addressable.beInfo) *)
  Info* = POINTER TO InfoDesc;
  InfoDesc* = RECORD
    (D.InfoDesc)
    name*: D.String;
    (* C name assigned to an Oberon-2 object *)
    callConv*: INTEGER;
    (* for a procedure type this string represents the calling convention that
       has to be used when activating the procedure resp. variable; if not 
       specified by the back-end (see SystemFlags.StructModifiers), then this
       is set to `StandardCallConv()' *)
    givenName-: D.String;
    (* not NIL if the link name is explicitly set in the external module; this
       value will be used for the `name' field above and overides the default
       name mangling *)
    link-: External.Ref;
    (* holds the entries of the link section of an external module *)
    library*: External.Lib;
    (* not NIL if the module's code is part of the named library *)
  END;


PROCEDURE CreateInfo* (adr: D.Addressable);
  VAR
    info: Info;
  BEGIN
    IF (adr. beInfo = NIL) THEN
      NEW (info);
      info. name := NIL;
      info. givenName := NIL;
      info. link := NIL;
      info. callConv := -1;
      info. library := NIL;
      adr. beInfo := info
    END
  END CreateInfo;

PROCEDURE StandardCallConv(): INTEGER;
  BEGIN
    (* The following doesn't work, because FOREIGN modules are declared as
       FOREIGN "C" and cannot use any native oo2c module that uses the calling
       convention "Pascal".  For an example check out how PosixFileDescr 
       dependends on Channel.
       
    IF (StdPragmas.targetOS. value^ = "Win32") THEN
      RETURN callConvPascal
    ELSE
      RETURN callConvC
    END*)
    
    RETURN callConvC
  END StandardCallConv;


PROCEDURE Ident (str: ARRAY OF CHAR): BOOLEAN;
  BEGIN
    RETURN (S.sym = S.ident) & (S.str^ = str)
  END Ident;

PROCEDURE String (VAR str: ARRAY OF CHAR);
  BEGIN
    IF (S.sym = S.string) THEN
      COPY (S.str^, str)
    ELSE
      E.Err (S.currSymPos, 137);         (* string expected *)
      COPY ("", str)
    END;
    S.GetSym
  END String;

PROCEDURE HeapString(): D.String;
  VAR
    str: ARRAY 256 OF CHAR;
    s: D.String;
  BEGIN
    String (str);
    NEW (s, Strings.Length (str)+1);
    COPY (str, s^);
    RETURN s
  END HeapString;

PROCEDURE CheckIdent (str: ARRAY OF CHAR);
  BEGIN
    IF ~Ident (str) THEN
      E.ErrIns (S.currSymPos, 500, str)  (* identifier expected *)
    END;
    S.GetSym
  END CheckIdent;

PROCEDURE File (VAR file, suffix: D.String);
  VAR
    len, i: INTEGER;
  BEGIN
    file := HeapString();
    len := Strings.Length (file^);
    i := len-1;
    WHILE (i >= 0) & (file[i] # ".") DO
      DEC (i)
    END;
    IF (i >= 0) THEN
      NEW (suffix, len-i+1);
      Strings.Extract (file^, i, len-i, suffix^)
    ELSE
      NEW (suffix, 1);
      suffix[0] := 0X
    END;
    file[i] := 0X
  END File;


PROCEDURE SetFlag (adr: D.Addressable);
  VAR
    i: INTEGER;
  
  PROCEDURE Set (VAR set: SET; index: SHORTINT);
    BEGIN
      IF (index IN set) THEN
        E.Err (S.currSymPos, -600)  (* warning: this flag is already set *)
      ELSE
        INCL (set, index)
      END
    END Set;
  
  BEGIN  (* pre: S.sym = S.string *)
    i := 0;
    WHILE (i # LEN (mods)) & (mods[i]. name # S.str^) DO
      INC (i)
    END;
    IF (i = LEN (mods)) THEN
      E.Err (S.currSymPos, 501)  (* undefined flag name *)
    ELSIF (adr IS D.Object) & (mods[i]. objFlag < 0) THEN
      E.Err (S.currSymPos, 502)  (* flag only applies to types *)
    ELSIF (adr IS D.Struct) & (mods[i]. structFlag < 0) THEN
      E.Err (S.currSymPos, 503)  (* flag only applies to declarations *)
    ELSIF (adr IS D.Object) THEN
      (* any checks that inspect the object's type have to be done in the
         second call to ObjectModifiers with parse=FALSE *)
      IF (mods[i]. objId = {}) THEN
        Set (adr(D.Object). beFlags, mods[i]. objFlag)
      ELSE
        Set (adr(D.Object). flags, mods[i]. objFlag)
      END
    ELSE (* adr IS D.Struct *) 
      IF (adr(D.Struct). form >= strOffset) &
         (adr(D.Struct). form-strOffset <= MAX (SET)) &
         (adr(D.Struct). form-strOffset IN mods[i]. structId) THEN
        IF (mods[i]. structFlag >= offsetBE) THEN
          Set (adr(D.Struct). beFlags, mods[i]. structFlag-offsetBE)
        ELSE
          Set (adr(D.Struct). flags, mods[i]. structFlag)
        END
      ELSE
        E.Err (S.currSymPos, 505)  (* can't use this flag here *)
      END
    END;
    S.GetSym
  END SetFlag;

PROCEDURE CallConv (): INTEGER;
  VAR
    callConv: INTEGER;
    callConvStr: ARRAY 16 OF CHAR;
  BEGIN
    (* parse and check calling convention *)
    String (callConvStr);
    IF (callConvStr = "C") THEN
      callConv := callConvC
    ELSIF (StdPragmas.targetOS. value^ = "Win32") & 
          (callConvStr = "Pascal") THEN
      callConv := callConvPascal
    ELSE
      E.Err (S.currSymPos, 508);  (* calling convention not supported *)
      callConv := StandardCallConv()
    END;
    RETURN callConv
  END CallConv;

PROCEDURE ModuleModifiers (mod: D.Object; parse: BOOLEAN);
  VAR
    lib: External.Lib;
    ref: External.Ref;
    
  PROCEDURE LinkSection;
    VAR
      str, file, suffix: D.String;
      pos: LONGINT;
      ef: External.File;
    
    PROCEDURE AddOptionClause (VAR prefix, suffix: External.NameList);
      BEGIN
        IF Ident ("ADD_OPTION") THEN
          S.GetSym;
          IF (S.sym = S.ident) THEN
            NEW (str, Strings.Length (S.str^)+1);
            COPY (S.str^, str^);
            External.AddName (prefix, str)
          ELSE
            E.Err (S.currSymPos, 100)  (* identifier expected *)
          END;
          S.GetSym;
          IF (S.sym = S.comma) THEN
            S.GetSym;
            IF (S.sym = S.ident) THEN
              NEW (str, Strings.Length (S.str^)+1);
              COPY (S.str^, str^);
              External.AddName (suffix, str)
            ELSE
              E.Err (S.currSymPos, 100)  (* identifier expected *)
            END;
            S.GetSym
          END
        END
      END AddOptionClause;
    
    BEGIN
      pos := S.currSymPos;
      IF Ident ("FILE") THEN
        S.GetSym;
        File (file, suffix);
        ef := External.NewFile (External.fileRef, file^, suffix^, pos);
        External.Append (mod. beInfo(Info). link, ef);
        AddOptionClause (ef. prefixOptions, ef. suffixOptions)
      ELSIF Ident ("OBJ") THEN
        S.GetSym;
        File (file, suffix);
        External.Append (mod. beInfo(Info). link, 
          External.NewFile (External.fileRef, file^, suffix^, pos))
      ELSIF Ident ("LIB") THEN
        S.GetSym;
        str := HeapString();
        lib := External.GetLib (External.libRef, str^, "");
        External.Append (mod. beInfo(Info). link, lib);
        
        IF (S.sym = S.lParen) THEN
          (* parse dependence list *)
          LOOP
            S.GetSym;
            str := HeapString();
            External.AppendDep (lib, str);
            IF (S.sym # S.comma) THEN
              EXIT
            END
          END;
          S.CheckSym (S.rParen)
        END;
        
        AddOptionClause (lib. prefixOptions, lib. suffixOptions)
      ELSE
        E.Err (S.currSymPos, 506);  (* FILE, OBJ, or LIB expected *)
        S.GetSym
      END
    END LinkSection;
  
  PROCEDURE SetFlag (id: INTEGER);
    BEGIN
      IF (id IN mod. beFlags) THEN
        E.Err (S.currSymPos, -600)  (* warning: flag already set *)
      END;
      INCL (mod. beFlags, id)
    END SetFlag;
  
  PROCEDURE ReadLibrary (VAR lib: External.Lib);
    VAR
      name, version: D.String;
    BEGIN
      name := HeapString();
      version := HeapString();
      lib := External.GetLib (External.libRef, name^, version^);
      S.CheckSym (S.semicolon)
    END ReadLibrary;
  
  PROCEDURE NormalModule;
    BEGIN
      mode := normal;
      mod. beFlags := mod. beFlags+{StdTypes.objCodeFile, StdTypes.objInitFct};

      IF (StdTypes.objInLibrary IN mod. beFlags) THEN
        ref := mod. beInfo(Info). link;
        WHILE (ref # NIL) & (ref. mode # External.objRef) DO
          ref := ref. next
        END;
        IF (ref # NIL) THEN
           E.Err (mod. pos, 513)
           (* can't create library if a module links in an object file *)
        END
      END
    END NormalModule;
  
  BEGIN
    IF parse THEN
      IF (S.sym = S.lBrak) THEN
        S.GetSym;
        IF Ident ("OOC_EXTENSIONS") THEN
          S.GetSym;
          INCL (mod. flags, D.objAllowsSystemFlags);
          NormalModule
        ELSE
          CreateInfo (mod);
          INCL (mod. flags, D.objExportsBEInfo);

          IF Ident ("LIBRARY") THEN
            S.GetSym;
            ReadLibrary (mod. beInfo(Info). library);
            INCL (mod. beFlags, StdTypes.objLibraryMaster)
          END;

          IF Ident ("INTERFACE") THEN
            mode := interface;
            INCL (mod. flags, D.objAllowsSystemFlags);
            INCL (mod. beFlags, StdTypes.objInterfaceModule)
          ELSIF Ident ("FOREIGN") THEN
            mode := foreign;
            INCL (mod. flags, D.objAllowsSystemFlags);
            mod. beFlags := mod. beFlags+{StdTypes.objForeignModule, StdTypes.objInitFct}
          ELSE
            E.Err (S.currSymPos, 507);  (* FOREIGN or INTERFACE expected *)
            mode := interface
          END;
          S.GetSym;

          (* parse and check calling convention *)
          callConv := CallConv();

          WHILE (S.sym = S.comma) DO
            S.GetSym;
            IF Ident ("CODE_FILE") THEN
              SetFlag (StdTypes.objCodeFile)
            ELSIF Ident ("INIT_FCT") THEN
              SetFlag (StdTypes.objInitFct)
            ELSE
              E.Err (S.currSymPos, 512)  (* module flag expected *)
            END;
            S.GetSym
          END;

          IF (S.sym = S.semicolon) THEN
            S.GetSym;
            CheckIdent ("LINK");
            LOOP
              LinkSection;
              IF (S.sym # S.semicolon) THEN
                EXIT
              END;
              S.GetSym
            END;
            S.CheckSym (S.end)
          END
        END;

        S.CheckSym (S.rBrak)
      ELSE
        NormalModule
      END
    END
  END ModuleModifiers;

PROCEDURE ObjectModifiers* (obj: D.Object; parse: BOOLEAN);
(* Called by module `ParseDecl' to parse an object's back-end specific flags
   if `parse=TRUE', otherwise to check the flags' semantics.  Note that this
   procedure has to check if a set of modifiers is following, ie it has to 
   check for `S.sym=S.lBrak' before doing any parsing.  
   See frontend/doc/Modifiers for details, including the places where this 
   procedure is called.  *)
  VAR
    const: D.Const;
    i, j: LONGINT;
    set: SET;
    record: D.Struct;

  PROCEDURE ValidForObject (obj: D.Object; ids: SET): BOOLEAN;
    VAR
      i: SHORTINT;
      valid: BOOLEAN;
    BEGIN
      FOR i := 0 TO MAX (SET) DO
        IF (i IN ids) THEN
          CASE i OF
          | objOpenArrayParam:
            valid := (D.objIsParameter IN obj. flags) &
                     (obj. type. form = D.strOpenArray)
          | objReferenceParam:
            valid := (D.objIsParameter IN obj. flags) &
                     StdTypes.PassPerReference (obj, TRUE)
          | objVarRecordParam:
            valid := (obj. mode = D.objVarPar) &
                     (obj. type. form = D.strRecord)
          | objStructValueParam:
            valid := (obj. mode = D.objVar) &
                     (D.objIsParameter IN obj. flags) &
                     Sym.TypeInGroup (obj. type, D.grpStructured)
          ELSE
            valid := (obj. mode = i)
          END;
          IF valid THEN
            RETURN TRUE
          END
        END
      END;
      RETURN FALSE
    END ValidForObject;
  
  BEGIN
    IF (obj. mode = D.objModule) THEN  (* module header *)
      ModuleModifiers (obj, parse)
    ELSE
      IF parse THEN
        CreateInfo (obj);
        INCL (obj. flags, D.objExportsBEInfo);
        
        (* set flags that apply per default *)
        IF (mode # normal) OR 
           (obj. mode # D.objProc) &(obj. mode # D.objTBProc) THEN
          EXCL (obj. flags, D.objHasBody)
        END;
        
        S.allowUnderscore := TRUE;
        IF (S.sym = S.lBrak) THEN
          IF ~(D.objAllowsSystemFlags IN Sym.mod. flags) THEN
            E.Err (S.currSymPos, 509)  (* flags not allowed in module *)
          END;
          REPEAT
            S.GetSym;
            IF (S.sym = S.ident) & (S.str^ = "PROC_ID") THEN
              (* we are setting the procedure id for a special code procedure*)
              IF (D.objIsSpecialCodeProc IN obj. flags) THEN
                E.Err (S.currSymPos, -600) (* warning: flags already set *)
              END;
              INCL (obj. flags, D.objIsSpecialCodeProc);
              NEW (const);
              D.InitConst (const, NIL);
              obj. data := const;
              S.GetSym;
              S.CheckSym (S.eql);
              IF (S.sym = S.number) & (S.numType = S.numInt) &
                 (S.intVal > 0) THEN
                const. int := S.intVal
              ELSE
                E.Err (S.currSymPos, 255) (* need non-zero integer const *)
              END;
              S.GetSym
            ELSIF (S.sym = S.ident) THEN
              SetFlag (obj)
            ELSIF (S.sym = S.string) THEN
              IF (StdTypes.objFixedName IN obj. beFlags) THEN
                E.Err (S.currSymPos, 510) (* link name already specified *)
              END;
              INCL (obj. beFlags, StdTypes.objFixedName);
              NEW (obj. beInfo(Info). givenName, Strings.Length (S.str^)+1);
              COPY (S.str^, obj. beInfo(Info). givenName^);
              S.GetSym
            ELSE
              E.Err (S.currSymPos, 511); (* flag or string expected *)
              S.GetSym
            END
          UNTIL (S.sym # S.comma);
          S.CheckSym (S.rBrak)
        END;
        S.allowUnderscore := (D.objAllowsUnderscore IN Sym.mod. flags)
        
      ELSE
        (* scan through the backend specific flags of the object, identify
           the system flag the sets it, and check if the flag can be used
           at this place *)
        set := obj. flags*{D.objHasBody, D.objNoLengthTag, D.objNoTypeTag, 
                           D.objNilCompat};
        i := 0;
        WHILE (i <= MAX (SET)) DO
          IF (i IN set) THEN
            j := 0;
            WHILE (mods[j]. objFlag # i) DO
              INC (j)
            END;
            IF ValidForObject (obj, mods[j]. objId) THEN
              IF (mode = interface) & (j = D.objHasBody) &
                 ~(StdTypes.objCodeFile IN Sym.mod. beFlags) THEN
                E.Err (obj. pos, 504)  (* no proc body without CODE_FILE *)
              END
            ELSE
              E.ErrIns (obj. pos, 516, mods[j]. name)  
              (* flag not applicable to this object *)
            END
          END;
          INC (i)
        END;
        IF (D.objAbstractTBProc IN obj. flags) THEN
          record := obj. data(D.Object). type;
          IF (record. form = D.strPointer) THEN
            record := record. base
          END;
          IF ~(D.structAbstractType IN record. flags) THEN
            E.Err (obj. pos, 452)  (* receiver type not declared "abstract" *)
          END;
          IF ~(D.objIsExported IN obj. flags) THEN
            E.Err (obj. pos, 455)  (* abstract proc must be exported *)
          END
        END;
        
        IF (obj. mode = D.objVarPar) & (obj. type. form = D.strRecord) &
           ((mode = interface) OR 
            (D.structNoDescriptor IN obj. type. flags)) THEN
          (* a variable record parameter has no type tag in interface modules
             or if the record type has to type descriptor *)
          INCL (obj. flags, D.objNoTypeTag)
        END;
        
        IF (D.objIsParameter IN obj. flags) & 
           (obj. type. form = D.strOpenArray) &
           ((mode = interface) OR 
            (D.structNoLengthInfo IN obj. type. flags)) THEN
          (* an open array parameter has no type tag in interface modules
             or if the array type doesn't have any length information at all;
             without knowledge of its length it is not possible to create a
             local copy of an open array value parameter *)
          INCL (obj. flags, D.objNoLengthTag);
          IF (obj. mode = D.objVar) THEN  (* value parameter *)
            INCL (obj. beFlags, StdTypes.objNoLocalCopy)
          END
        END;
        
        IF (StdTypes.objNoLocalCopy IN obj. beFlags) &
           ~ValidForObject (obj, {objStructValueParam}) THEN
          E.ErrIns (obj. pos, 516, mods[16]. name)  
          (* flag not applicable to this object *)
        END
      END
    END
  END ObjectModifiers;

PROCEDURE StructModifiers* (str: D.Struct; parse: BOOLEAN);
(* Called by module `ParseDecl' to parse a type's back-end specific flags
   if `parse=TRUE', otherwise to check the flags' semantics.  Note that this
   procedure has to check if a set of modifiers is following, ie it has to 
   check for `S.sym=S.lBrak' before doing any parsing.  
   See frontend/doc/Modifiers for details, including the places where this 
   procedure is called.  *)
  
  PROCEDURE HasRestParam (str: D.Struct): BOOLEAN;
    VAR
      param: D.Object;
    BEGIN
      param := str. decl;
      WHILE (param # NIL) DO
        IF (param. mode = D.objRestParam) THEN
          RETURN TRUE
        END;
        param := param. rightObj
      END;
      RETURN FALSE
    END HasRestParam;
  
  BEGIN
    IF parse THEN
      CreateInfo (str);
      INCL (str. flags, D.structExportsBEInfo);
        
      (* set flags that apply per default *)
      IF (mode = interface) THEN
        CASE str. form OF
        | D.strRecord: 
          str. flags := str. flags + {D.structNoDescriptor, D.structNotExtensible}
        | D.strArray: 
          str. flags := str. flags + {D.structNoDescriptor}
        | D.strOpenArray: 
          str. flags := str. flags + {D.structNoDescriptor, D.structNoLengthInfo}
        | D.strPointer:
          str. flags := str. flags + {D.structStaticPointer, D.structDisableNew}
        | D.strProc:
          str. flags := str. flags + {D.structEnableRestParam}
        ELSE
        END
      END;
      
      S.allowUnderscore := TRUE;
      IF (S.sym = S.lBrak) THEN
        IF ~(D.objAllowsSystemFlags IN Sym.mod. flags) THEN
          E.Err (S.currSymPos, 509)  (* flags not allowed in this module *)
        END;
        REPEAT
          S.GetSym;
          IF (S.sym = S.ident) THEN
            SetFlag (str)
          ELSIF (S.sym = S.string) & (str. form = D.strProc) THEN
            str. beInfo(Info). callConv := CallConv()
          ELSE
            IF (str. form = D.strProc) THEN
              E.Err (S.currSymPos, 511)  (* flag or string expected *)
            ELSE
              E.Err (S.currSymPos, 512)  (* flag expected *)
            END;
            S.GetSym
          END
        UNTIL (S.sym # S.comma);
        S.CheckSym (S.rBrak)
      END;
      S.allowUnderscore := (D.objAllowsUnderscore IN Sym.mod. flags)
      
    ELSE  (* fill in additional information and do some semantic checks *)
      IF (str. form = D.strPointer) THEN
        IF (D.structNoDescriptor IN str. base. flags) THEN
          INCL (str. flags, D.structStaticPointer)
        END;
        IF ((str. flags+str. base. flags) * 
            {D.structNoDescriptor, D.structUnion, D.structNoLengthInfo,
             D.structStaticPointer} # {}) THEN
          INCL (str. flags, D.structDisableNew)
        END;
        IF (D.structCArrayAssign IN str. flags) &
           ((str. base. form # D.strArray) &
            (str. base. form # D.strOpenArray) OR
            ~Sym.TypeInGroup (str. base. base, D.grpChar)) THEN
          E.Err (str. base. pos, 519)  
          (* CSTRING only for pointer to character array *)
        END
      END;
      
      IF (str. form = D.strProc) THEN
        IF (str. beInfo(Info). callConv < 0) THEN
          IF (mode # normal) THEN
            (* calling convention wasn't specified by user, so we use the one 
               given in the module header *)
            str. beInfo(Info). callConv := callConv
          ELSE
            str. beInfo(Info). callConv := StandardCallConv()
          END
        END;

        IF (str. beInfo(Info). callConv # StandardCallConv()) THEN
          INCL (str. beFlags, StdTypes.structSpecialCallConv)
        END;
        
        IF HasRestParam (str) THEN
          IF (str. decl. mode = D.objRestParam) THEN
            E.Err (str. decl. pos, 517)  (* `...' must follow normal param *)
          END;
          IF (str. beInfo(Info). callConv # callConvC) THEN
            E.Err (str. decl. pos, 518)  (* call conv doesn't support `...' *)
          END
        END
      END;
      
      IF (str. form = D.strRecord) THEN
        CreateInfo (str);
        INCL (str. flags, D.structExportsBEInfo)
      END;
      
      IF (str. form = D.strOpenArray) & (D.structNoLengthInfo IN str. flags) & 
         (str. base. form = D.strOpenArray) THEN
        (* open array without length information has open array as element 
           type *)
        E.Err (str. base. pos, 208)  (* can't use open array here *)
      END
    END
  END StructModifiers;



PROCEDURE WriteObjectInfo* (w: BinaryRider.Writer; obj: D.Object);
(* Writes relevant parts of `obj. beInfo' into the symbol file.  Called from
   module `SymbolTable' when writing objects (incl the module) out to the file
   if `D.objExportsBEInfo IN obj. flags'.  `w' is a valid writer at the correct
   file position.
   Note that it is also possible to extend `obj. flags' with information for 
   the symbol file.  In this case the value of `D.objExportMask' has to be
   adjusted.  *)
  BEGIN
    IF (obj. mode = D.objModule) THEN
      IF (StdTypes.objLibraryMaster IN obj. beFlags) THEN
        External.WriteString (w, obj. beInfo(Info). library. name^);
        External.WriteString (w, obj. beInfo(Info). library. version^)
      ELSIF (StdTypes.objInLibrary IN obj. beFlags) THEN
        External.WriteString (w, obj. beInfo(Info). library. name^)
      ELSE
        (* if a module is made part of a library all its external references
           become obsolete; C code will be moved into the library, object files
           aren't valid, and libraries will turn into library references of the
           library being built *)
        External.WriteRefList (w, obj. beInfo(Info). link)
      END
    ELSIF (StdTypes.objFixedName IN obj. beFlags) THEN
      External.WriteString (w, obj. beInfo(Info). givenName^)
    END;
    IF (D.objIsSpecialCodeProc IN obj. flags) THEN
      w. WriteLInt (obj. data(D.Const). int)
    END
  END WriteObjectInfo;

PROCEDURE ReadObjectInfo* (r: BinaryRider.Reader; obj: D.Object);
(* Reads `obj. beInfo' from the symbol file.  Called from module `SymbolTable'
   when reading an object from the file that has `D.objExportsBEInfo' set.  `r'
   is a valid rider at the correct file position.  This procedure has to mirror
   `WriteObjectInfo' completely or otherwise the symbol files will break.  *)
  VAR
    const: D.Const;
    name, version: D.String;
    lib: External.Lib;
  BEGIN
    CreateInfo (obj);
    IF (obj. mode = D.objModule) THEN
      IF (StdTypes.objLibraryMaster IN obj. beFlags) THEN
        name := External.ReadString (r);
        version := External.ReadString (r);
        lib := External.GetLib (External.libRef, name^, version^);
        IF noLibFileRead THEN
          lib. deferred := TRUE
        ELSE
          External.ReadLibFile (lib, S.currSymPos)
        END;
        obj. beInfo(Info). library := lib
      ELSIF (StdTypes.objInLibrary IN obj. beFlags) THEN
        name := External.ReadString (r);
        lib := External.GetLib (External.libRef, name^, "");
        IF noLibFileRead THEN
          lib. deferred := TRUE
        ELSE
          External.ReadLibFile (lib, S.currSymPos)
        END;
        obj. beInfo(Info). library := lib
      ELSE
        obj. beInfo(Info). link := External.ReadRefList (r)
      END
    ELSIF (StdTypes.objFixedName IN obj. beFlags) THEN
      obj. beInfo(Info). givenName := External.ReadString (r);
    END;
    IF (D.objIsSpecialCodeProc IN obj. flags) THEN
      NEW (const);
      D.InitConst (const, NIL);
      obj. data := const;
      r. ReadLInt (obj. data(D.Const). int)
    END
  END ReadObjectInfo;

PROCEDURE WriteStructInfo* (w: BinaryRider.Writer; struct: D.Struct);
(* Writes relevant parts of `struct. beInfo' into the symbol file.  Called from
   module `SymbolTable' when writing types (ie entities of type `D.Struct' out
   to the file if `D.structExportsBEInfo IN obj. flags'.  `w' is a valid writer
   at the correct file position. 
   Note that it is also possible to extend `struct. flags' with information for
   the symbol file.  In this case the value of `D.structExportMask' has to be
   adjusted.  *)
  BEGIN
    IF (struct. form = D.strRecord) THEN
      (* an unnamed record that appears as part of an exported type declaration
         may appear in generated type expressions in the importing modules; for
         this reason its C name has to be known outside the exporting file *)
      IF (struct. obj = NIL) THEN
        External.WriteString (w, struct. beInfo(Info). name^)
      ELSE
        External.WriteString (w, emptyString)
      END
    ELSIF (struct. form = D.strProc) & 
          (StdTypes.structSpecialCallConv IN struct. beFlags) THEN
      w. WriteNum (struct. beInfo(Info). callConv)
    END
  END WriteStructInfo;

PROCEDURE ReadStructInfo* (r: BinaryRider.Reader; struct: D.Struct);
(* Reads `struct. beInfo' from the symbol file.  Called from module 
   `SymbolTable' when reading an object from the file that has 
   `D.objExportsBEInfo' set.  `r' is a valid rider at the correct file 
   position.  This procedure has to mirror `WriteStructInfo' completely or the
   symbol files will be break.  *)
  VAR
    i: LONGINT;
    name: D.String;
  BEGIN
    CreateInfo (struct);
    IF (struct. form = D.strRecord) THEN
      name := External.ReadString (r);
      IF (name^ = "") THEN
        name := NIL
      END;
      struct. beInfo(Info). name := name
    ELSIF (struct. form = D.strProc) THEN
      IF (StdTypes.structSpecialCallConv IN struct. beFlags) THEN
        r. ReadNum (i);
        struct. beInfo(Info). callConv := SHORT (i)
      ELSE
        struct. beInfo(Info). callConv := StandardCallConv()
      END
    END
  END ReadStructInfo;


PROCEDURE ParamsMatchExt (str1, str2: D.Struct): BOOLEAN;
(* This procedure extends the predicate SymbolTable.ParamsMatch.  It tests the
   compability of back-end specific attributes that aren't part of a normal 
   Oberon-2 procedure type, like calling convention and parameter locations.  
   It's only called after it's asserted that `str1' and `str2' are matching
   formal parameter lists in the Oberon-2 sense.  This implies that both are
   procedure types, have the same number of formal parameters, and that the
   parameters match.  
   This procedure is assigned to the variable SymbolTable.paramsMatchExt. *)
  VAR
    p0, p1: D.Object;
    c1, c2: INTEGER;
  BEGIN
    p0 := str1. decl; p1 := str2. decl;
    WHILE (p0 # NIL) DO
      IF ((p0. flags / p1. flags) * {D.objNoTypeTag, D.objNoLengthTag} # {}) THEN
        (* one argument is passed together with type resp. length tag, the
           other isn't; therefore the number of arguments on assembler level
           differs and the procedure types are incompatible *)
        RETURN FALSE
      END;
      p0 := p0. rightObj; p1 := p1. rightObj
    END;
    (* check that both procedures utilize the same calling conventions *)
    IF (str1. beInfo # NIL) THEN
      c1 := str1. beInfo(Info). callConv
    ELSE
      c1 := StandardCallConv()
    END;
    IF (str2. beInfo # NIL) THEN
      c2 := str2. beInfo(Info). callConv
    ELSE
      c2 := StandardCallConv()
    END;
    (* also make sure that certain flags don't differ for the two procedures *)
    RETURN (c1 = c2)
  END ParamsMatchExt;


BEGIN
  mods[0]. name := "NOT_EXTENSIBLE"; 
  mods[0]. objId := {};
  mods[0]. objFlag := -1;
  mods[0]. structId := {D.strRecord-strOffset}; 
  mods[0]. structFlag := D.structNotExtensible;
  
  mods[1]. name := "NO_DESCRIPTOR"; 
  mods[1]. objId := {};
  mods[1]. objFlag := -1;
  mods[1]. structId := {D.strRecord-strOffset, D.strArray-strOffset, 
                        D.strOpenArray-strOffset};
  mods[1]. structFlag := D.structNoDescriptor;
  
  mods[2]. name := "NO_LENGTH_INFO"; 
  mods[2]. objId := {};
  mods[2]. objFlag := -1;
  mods[2]. structId := {D.strOpenArray-strOffset};
  mods[2]. structFlag := D.structNoLengthInfo;
  
  mods[3]. name := "NO_LENGTH_TAG"; 
  mods[3]. objId := {objOpenArrayParam};
  mods[3]. objFlag := D.objNoLengthTag;
  mods[3]. structId := {};
  mods[3]. structFlag := -1;
  
  mods[4]. name := "NO_TYPE_TAG"; 
  mods[4]. objId := {objVarRecordParam};
  mods[4]. objFlag := D.objNoTypeTag;
  mods[4]. structId := {};
  mods[4]. structFlag := -1;
  
  mods[5]. name := "STATIC_POINTER"; 
  mods[5]. objId := {};
  mods[5]. objFlag := -1;
  mods[5]. structId := {D.strPointer-strOffset};
  mods[5]. structFlag := D.structStaticPointer;
  
  mods[6]. name := "DISABLE_NEW"; 
  mods[6]. objId := {};
  mods[6]. objFlag := -1;
  mods[6]. structId := {D.strPointer-strOffset};
  mods[6]. structFlag := D.structDisableNew;
  
  mods[7]. name := "NIL_COMPAT"; 
  mods[7]. objId := {objReferenceParam};
  mods[7]. objFlag := D.objNilCompat;
  mods[7]. structId := {};
  mods[7]. structFlag := -1;
  
  mods[8]. name := "HAS_BODY"; 
  mods[8]. objId := {D.objProc, D.objTBProc};
  mods[8]. objFlag := D.objHasBody;
  mods[8]. structId := {};
  mods[8]. structFlag := -1;
  
  mods[9]. name := "UNION"; 
  mods[9]. objId := {};
  mods[9]. objFlag := -1;
  mods[9]. structId := {D.strRecord-strOffset};
  mods[9]. structFlag := D.structUnion;
  
  mods[10]. name := "CSTRING"; 
  mods[10]. objId := {};
  mods[10]. objFlag := -1;
  mods[10]. structId := {D.strPointer-strOffset};
  mods[10]. structFlag := D.structCArrayAssign;
  
  mods[11]. name := "ALIGN1"; 
  mods[11]. objId := {};
  mods[11]. objFlag := -1;
  mods[11]. structId := {D.strRecord-strOffset};
  mods[11]. structFlag := StdTypes.structAlign1+offsetBE;
  
  mods[12]. name := "ALIGN2"; 
  mods[12]. objId := {};
  mods[12]. objFlag := -1;
  mods[12]. structId := {D.strRecord-strOffset};
  mods[12]. structFlag := StdTypes.structAlign2+offsetBE;
  
  mods[13]. name := "ALIGN4"; 
  mods[13]. objId := {};
  mods[13]. objFlag := -1;
  mods[13]. structId := {D.strRecord-strOffset};
  mods[13]. structFlag := StdTypes.structAlign4+offsetBE;
  
  mods[14]. name := "ALIGN8"; 
  mods[14]. objId := {};
  mods[14]. objFlag := -1;
  mods[14]. structId := {D.strRecord-strOffset};
  mods[14]. structFlag := StdTypes.structAlign8+offsetBE;
  
  mods[15]. name := "ABSTRACT"; 
  mods[15]. objId := {D.objTBProc};
  mods[15]. objFlag := D.objAbstractTBProc;
  mods[15]. structId := {D.strRecord-strOffset};
  mods[15]. structFlag := D.structAbstractType;
  
  mods[16]. name := "NO_COPY"; 
  mods[16]. objId := {};
  mods[16]. objFlag := StdTypes.objNoLocalCopy;
  mods[16]. structId := {};
  mods[16]. structFlag := -1;
  
  Sym.paramsMatchExt := ParamsMatchExt;
  noLibFileRead := FALSE;
  emptyString := ""
END SystemFlags.
