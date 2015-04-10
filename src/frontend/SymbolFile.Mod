(* 	$Id: SymbolFile.Mod,v 1.29 2002/01/12 22:16:33 ooc-devel Exp $	 *)
MODULE SymbolFile;
(*  Exporting and importing of symbol files.
    Copyright (C) 1995-1999, 2002  Michael van Acken

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

IMPORT
  SYSTEM, Strings, Files, BinaryRider, IntStr, Parameter, ParamPaths,
  Config, E := Error, D := Data, StdTypes, SystemFlags, Sym := SymbolTable;


CONST
  writeNotExportedFields = TRUE;
  (* if TRUE, write the names of fields and type-bound procedures into the 
     symbol file, even if they aren't exported, otherwise write the complete
     object information but replace the name by "" *)
     
CONST
  firstArray = 128-4;
  (* initial size of `structArray^', should fit closely into a 2^n block *)
  incrArray = 64;
  (* each time `structArray^' overflows, its size is incremented by this 
     amount *)
     
TYPE
  StructArray = POINTER TO ARRAY OF D.Struct;
  
VAR
  structArray: StructArray;
  structLen: LONGINT;
  (* list of structs; `Write' uses it to keep track of all written
     structs, `Read' needs it to reconstruct the type structure *)
  emptyString: ARRAY 2 OF CHAR;
  emptyStringPtr: D.String;
  
VAR
  symbolFileId*: ARRAY 5 OF CHAR;
  
  

PROCEDURE FindImportedModule* (modName: ARRAY OF CHAR): D.Object;
  VAR
    obj: D.Object;
  BEGIN
    IF (modName = "SYSTEM") THEN
      RETURN Sym.system
    ELSE
      obj := Sym.importedMods;
      WHILE (obj # NIL) & (obj. name^ # modName) DO
        obj := obj. rightObj
      END;
      RETURN obj
    END
  END FindImportedModule;

PROCEDURE RemoveImportedModule* (modName: ARRAY OF CHAR);
(* Remove the symbol information of module `modName' from memory, together with
   all modules that are depending on it.  Nothing is done if no such module is
   currently imported.  *)
  VAR
    mod, next: D.Object;
    
  PROCEDURE Remove (VAR list: D.Object): BOOLEAN;
  (* Removes object `modName' from `list' if such an object exists (result is
     TRUE), otherwise the list is unchanged and result is FALSE.  *)
    BEGIN
      IF (list = NIL) THEN
        RETURN FALSE
      ELSIF (list. data(D.Const). string^ = modName) THEN
        list := list. rightObj;
        RETURN TRUE
      ELSE
        RETURN Remove (list. rightObj)
      END
    END Remove;
  
  BEGIN
    IF Remove (Sym.importedMods) THEN  (* this module was imported *)
      mod := Sym.importedMods;
      WHILE (mod # NIL) DO
        next := mod. rightObj;
        IF Remove (mod. leftObj) THEN  (* `mod' imported module `modName' *)
          RemoveImportedModule (mod. data(D.Const). string^)
        END;
        mod := next
      END
    END
  END RemoveImportedModule;

PROCEDURE CreateModuleId (): INTEGER;
  BEGIN
    IF (Sym.importedMods = NIL) THEN
      RETURN Sym.currentModuleId+1
    ELSE
      RETURN Sym.importedMods. moduleId+1
    END    
  END CreateModuleId;

PROCEDURE IntegrateSymbols* (mod: D.Object; stripData: BOOLEAN);
(* Integrates the symbol table of `mod' into the data structure that holds the
   symbols of imported modules.  The idea is to keep the data of the compiled
   module in memory, since it is likely that is used for the next compilation.
   With `stripData=TRUE' all information that isn't part of a normal symbol
   file is removed (and will be collected by the gc).  Otherwise the data is 
   left intact.  In either case references to GSA code are not touched.  *)
  VAR
    mid: INTEGER;
    
  PROCEDURE IntegrateTree (VAR tree: D.Object);
    VAR
      list, o: D.Object;
    
    PROCEDURE IntegrateList (VAR list: D.Object);
      VAR
        obj, prev, next: D.Object;
        
      PROCEDURE ObjIsPtrBase (obj: D.Object): BOOLEAN;
      (* Result is TRUE if `obj' describes a type that can be used for a 
         pointer base type.  These objects are not removed, since they may
         be used for debugging output later on.  
         
         [Because I need to keep pointer types as well, the function's name
          is a misnomer.  I can't discard a pointer, if it is not exported, but
          appears as a receiver type of an exported type-bound procedure.
          Right now I believe that the whole `IntegrateSymbols' procedure is
          rather stupidly implemented ;-)  -- mva ] *)
        BEGIN
          RETURN (obj. mode = D.objType) & 
                 ((obj. type. form = D.strArray) OR 
                  (obj. type. form = D.strOpenArray) OR 
                  (obj. type. form = D.strRecord) OR
                  (obj. type. form = D.strPointer))
        END ObjIsPtrBase;
      
      BEGIN
        obj := list; prev := NIL;
        WHILE (obj # NIL) DO
          next := obj. rightObj;
          IF (obj. type # NIL) &
             (Sym.Unnamed (obj. type) OR (obj = obj. type. obj)) &
             ((obj. type. form = D.strRecord) OR
              (obj. type. form = D.strProc)) THEN
            IntegrateList (obj. type. decl)
          END;
          obj. currValue := NIL;
          obj. moduleId := mid;
          IF stripData & ~(D.objIsExported IN obj. flags) &
             (~(D.objIsParameter IN obj. flags) OR (obj. data # NIL)) &
             ~(obj. mode IN {D.objField, D.objTBProc}) & 
             ~ObjIsPtrBase (obj) THEN
            o := obj;
            IF (prev = NIL) THEN
              list := obj. rightObj
            ELSE
              prev. rightObj := obj. rightObj
            END;
            (* clear pointer fields for the conservative gc's sake *)
            o. name := NIL; o. leftObj := NIL; o. rightObj := NIL; 
            o. localTo := NIL; o. localDecl := NIL; o. data := NIL;
            o. greg := NIL
          ELSE
            IF ~writeNotExportedFields & 
               (obj. mode IN {D.objField, D.objTBProc}) THEN
              (* if this field/type-bound proc would be read from symbol file,
                 the name would not be present *)
              obj. name := emptyStringPtr
            END;
            IF (obj. mode IN {D.objProc, D.objTBProc}) THEN
              IF (obj. mode = D.objTBProc) THEN
                IntegrateList (obj. data(D.Object))
              END;
              IntegrateTree (obj. localDecl)
            ELSIF (obj. mode = D.objConst) THEN
              obj. data(D.Const). preserve := TRUE
            END;
            prev := obj
          END;
          obj := next
        END
      END IntegrateList;
    
    BEGIN
      list := Sym.TransformIntoList (tree);
      IntegrateList (list);
      tree := Sym.TransformIntoTree (list)
    END IntegrateTree;
  
  BEGIN
    mid := CreateModuleId();
    mod. moduleId := mid;
    IntegrateTree (mod. localDecl);
    
    mod. rightObj := Sym.importedMods;
    Sym.importedMods := mod
  END IntegrateSymbols;


PROCEDURE WriteString* (w: BinaryRider.Writer; VAR str: ARRAY OF CHAR);
  VAR
    len: INTEGER;
  BEGIN
    len := Strings.Length (str);
    w. WriteNum (len);
    w. WriteBytes (str, 0, len)
  END WriteString;

PROCEDURE WriteStringConst (w: BinaryRider.Writer; const: D.Const);
  VAR
    sizeChar: LONGINT;
  BEGIN
    sizeChar := D.struct[const. type. form+(D.strChar8-D.strStringConst8)]. size;
    w. WriteNum (const. int);
    w. WriteBytes (const. string^, 0, const. int*sizeChar)
  END WriteStringConst;

PROCEDURE ReadString* (r: BinaryRider.Reader): D.String;
  VAR
    s: D.String;
    len: LONGINT;
  BEGIN
    r. ReadNum (len);
    NEW (s, len+1);
    r. ReadBytes (s^, 0, len);
    s[len] := 0X;
    RETURN s
  END ReadString;

PROCEDURE ReadStringConst (r: BinaryRider.Reader; form: SHORTINT): D.Const;
  VAR
    s: D.String;
    len, sizeChar: LONGINT;
  BEGIN
    sizeChar := D.struct[form+(D.strChar8-D.strStringConst8)]. size;
    r. ReadNum (len);
    NEW (s, len*sizeChar);
    r. ReadBytes (s^, 0, len*sizeChar);
    RETURN D.GetStringConst (s^, len, D.struct[form])
  END ReadStringConst;


PROCEDURE AppendToStructArray (t: D.Struct);
  VAR
    i: LONGINT;
    new: StructArray;
  BEGIN
    IF (structLen = LEN (structArray^)) THEN
      NEW (new, LEN (structArray^)+incrArray);
      FOR i := 0 TO LEN (structArray^)-1 DO
        new[i] := structArray[i]
      END;
      structArray := new
    END;
    structArray[structLen] := t;
    INC (structLen)
  END AppendToStructArray;

PROCEDURE WriteFlags* (w: BinaryRider.Writer; flags: SET);
  BEGIN
    w. WriteNum (SYSTEM.VAL (LONGINT, flags))
  END WriteFlags;

PROCEDURE Write* (mod: D.Object; VAR newSymbolFile, symbolFileChanged: BOOLEAN);
  VAR
    f: Files.File;
    w: BinaryRider.Writer;
    i: LONGINT;
    fileName: Parameter.Filename;
    msg: ARRAY 256 OF CHAR;
    objPos, magicId, magicOld, importIndex: LONGINT;
    res: Files.Result;
  
  PROCEDURE MarkExportedObjects (root: D.Object);
  (* Marks all exported objects in the binary tree `root' and their 
     substructures with `objInSymbolFile', or `structInSymbolFile'.  *)
     
    PROCEDURE MarkObject (obj: D.Object);
    (* Marks `obj' and its substructures with `xxxInSymbolFile'.  *)

      PROCEDURE MarkStruct (t: D.Struct);
      (* Marks `t' and its substructures with `xxxInSymbolFile'.  *)
        VAR
          obj: D.Object;
        BEGIN
          IF (t # NIL) THEN
            t. marker := -1;
            IF (t. obj # NIL) & Sym.ImportedObject (mod, t. obj) THEN
              (* set flag that a type from an imported module is used in the
                 symbol file *)
              INCL (t. obj. localTo(D.Object). flags, D.objInSymbolFile)
            ELSIF ~(D.structInSymbolFile IN t. flags) THEN
              INCL (t. flags, D.structInSymbolFile);
              MarkStruct (t. base);
              obj := t. decl;
              WHILE (obj # NIL) DO
                MarkObject (obj);
                obj := obj. rightObj
              END;
              MarkObject (t. obj)
            END
          END
        END MarkStruct;
      
      BEGIN
        IF (obj # NIL) & ~(D.objInSymbolFile IN obj. flags) THEN
          INCL (obj. flags, D.objInSymbolFile);
          IF (obj. mode = D.objTBProc) THEN
            MarkObject (obj. data(D.Object))
          END;
          MarkStruct (obj. type)
        END
      END MarkObject;
    
    BEGIN
      IF (root # NIL) THEN
        MarkExportedObjects (root. leftObj);
        IF (D.objIsExported IN root. flags) THEN
          MarkObject (root)
        END;
        MarkExportedObjects (root. rightObj)
      END
    END MarkExportedObjects;
  
  PROCEDURE WriteObject (obj: D.Object);
    PROCEDURE WriteStruct (t: D.Struct);
      VAR
        mod: D.Object;
        
      PROCEDURE WriteObjList (obj: D.Object);
        BEGIN
          IF (obj = NIL) THEN
            w. WriteNum (0)
          ELSE
            WriteObject (obj);
            WriteObjList (obj. rightObj)
          END
        END WriteObjList;
      
      BEGIN
        IF (t. marker >= 0) THEN  (* structure has been written previously *)
          w. WriteNum (-t. marker)
        ELSIF (D.strBoolean <= t. form) & (t. form <= D.strNone) THEN
          (* predefined type *)
          w. WriteNum (t. form)
        ELSE
          t. marker := structLen;
          AppendToStructArray (t);
          IF ~Sym.LocalType (obj, t) THEN
            mod := Sym.Module (t. obj);
            w. WriteNum (mod. data(D.Const). int2);
            WriteString (w, t. obj. name^)
          ELSE
            w. WriteNum (t. form);
            WriteFlags (w, t. flags * D.structExportMask);
            WriteFlags (w, t. beFlags * StdTypes.structExportMaskBE);
            
            IF (t. form = D.strRecord) & (t. base = NIL) THEN
              WriteStruct (D.struct[D.strNone])
            ELSE
              WriteStruct (t. base)
            END;
            
            IF (D.structExportsBEInfo IN t. flags) THEN
              SystemFlags.WriteStructInfo (w, t)
            END;
            
            CASE t. form OF
            | D.strPointer, D.strOpenArray:
            | D.strProc, D.strRecord:
              WriteObjList (t. decl)
            | D.strArray:
              w. WriteNum (t. len)
            END
          END
        END
      END WriteStruct;
    
    BEGIN
      IF (obj. mode = D.objType) & (obj. type. obj = obj) THEN
        (* this is the type declaration that sets the name of `obj. type' *)
        w. WriteNum (-obj. mode)
      ELSE
        w. WriteNum (obj. mode)
      END;
      IF (obj. mode # D.objRestParam) THEN
        IF ~writeNotExportedFields & 
           (obj. mode IN {D.objField, D.objTBProc}) & 
           ~(D.objIsExported IN obj. flags) THEN
          (* omit name of not exported record fields *)
          WriteString (w, emptyString)  
        ELSE
          WriteString (w, obj. name^)
        END;
        WriteFlags (w, obj. flags * D.objExportMask);
        WriteFlags (w, obj. beFlags * StdTypes.objExportMaskBE);
        WriteStruct (obj. type);
        IF (D.objExportsBEInfo IN obj. flags) THEN
          SystemFlags.WriteObjectInfo (w, obj)
        END;
        IF (obj. mode = D.objConst) THEN
          CASE obj. type. form OF 
          | D.strBoolean..(D.strReal-1): 
            w. WriteNum (obj. data(D.Const). int)
          | D.strReal, D.strLongReal:
            w. WriteLReal (obj. data(D.Const). real)
          | D.strSet8..D.strSet64:
            w. WriteSet (obj. data(D.Const). set)
          | D.strStringConst8, D.strStringConst16:
            WriteStringConst (w, obj. data(D.Const))
          | D.strNil:  (* no value necessary *)
          END
        ELSIF (obj. mode = D.objTBProc) THEN
          w. WriteNum (obj. offset);
          WriteObject (obj. data(D.Object))
        END
      END
    END WriteObject;
  
  PROCEDURE WriteTree (obj: D.Object);
    BEGIN
      IF (obj # NIL) THEN
        WriteTree (obj. leftObj);
        IF (D.objInSymbolFile IN obj. flags) & (obj. mode # D.objModule) THEN
          WriteObject (obj)
        END;
        WriteTree (obj. rightObj)
      END
    END WriteTree;
  
  PROCEDURE WriteUsedImports;
  (* Write list of module that contribute types to the symbol file of this 
     module.  Take care to write the module names in alphabetic sequence.  *)
    VAR
      mod: D.Object;
    
    PROCEDURE GetModule (lowerBound: ARRAY OF CHAR): D.Object;
      VAR
        upperBound: D.Object;
        mod: D.Object;
      BEGIN
        upperBound := NIL;
        mod := Sym.importedMods;
        WHILE (mod # NIL) DO
          IF (D.objInSymbolFile IN mod. flags) &
             (lowerBound < mod. name^) &
             ((upperBound = NIL) OR (mod. name^ < upperBound. name^)) THEN
            upperBound := mod
          END;
          mod := mod. rightObj
        END;
        RETURN upperBound
      END GetModule;
    
    BEGIN
      mod := GetModule ("");
      WHILE (mod # NIL) DO
        mod. data(D.Const). int2 := importIndex;
        INC (importIndex);
        WriteString (w, mod. name^);
        w. WriteLInt (mod. data(D.Const). int);
        mod := GetModule (mod. name^)
      END
    END WriteUsedImports;
  
  PROCEDURE WriteOtherImports (obj: D.Object);
    VAR
      importedMod: D.Object;
    BEGIN
      IF (obj # NIL) THEN
        WriteOtherImports (obj. leftObj);
        IF (obj. mode = D.objModule) THEN
          importedMod := FindImportedModule (obj. data(D.Const). string^);
          IF ~(D.objInSymbolFile IN importedMod. flags) THEN
            WriteString (w, obj. data(D.Const). string^);
            w. WriteLInt (importedMod. data(D.Const). int);
            (* mark module; this avoids writing the same module to the symbol
               file even if it appears more than once in the IMPORT list *)
            INCL (importedMod. flags, D.objInSymbolFile)
          END
        END;
        WriteOtherImports (obj. rightObj)
      END
    END WriteOtherImports;
  
  PROCEDURE Fingerprint (f: Files.File; startPos: LONGINT; 
                         VAR key: ARRAY OF SYSTEM.BYTE);
  (* see Structured Programming(1993) 14: 136-147 
     pre: LEN(key) = fpSize *)
    CONST
      fpSize = SIZE(LONGINT);
    VAR
      r: BinaryRider.Reader;
      i, j, new, old: INTEGER;
      byte: CHAR;
    BEGIN
      r := BinaryRider.ConnectReader (f);
      FOR i := 0 TO fpSize-1 DO
        key[i] := 0
      END;
      i := 0; j := 0;
      (* calculate fp *)
      r. SetPos (startPos);
      r. ReadChar (byte);
      WHILE (r. res = BinaryRider.done) DO
        old := ORD (SYSTEM.VAL (CHAR, key[i]));
        new := ORD (SYSTEM.VAL (CHAR, SYSTEM.ROT (byte, j)));
        key[i] := CHR ((old+new) MOD 256);
        INC (i); 
        IF (i = fpSize) THEN
          j := (j + 1) MOD 8; i := 0
        END;
        r. ReadChar (byte)
      END
    END Fingerprint;

  PROCEDURE GetPreviousMagic (VAR magic: LONGINT): BOOLEAN;
    VAR
      fileName: Parameter.Filename;
      f: Files.File;
      r: BinaryRider.Reader;
      symId: ARRAY 5 OF CHAR;
      res: Files.Result;
    BEGIN
      IF ParamPaths.FindPathExt (mod. name^, Config.symbolExtension, 
                                 FALSE, fileName) THEN
        f := Files.Old (fileName, {Files.read}, res);
        IF (f # NIL) THEN
          r := BinaryRider.ConnectReader(f);
          symId := "XXXX";
          r. ReadBytes (symId, 0, 4);
          IF (symId = symbolFileId) THEN
            r. ReadLInt (magic);
            f. Close;
            RETURN (r. res = BinaryRider.done)
          ELSE
            f. Close
          END
        END
      END;
      RETURN FALSE
    END GetPreviousMagic;
  
  PROCEDURE ClearImportedMods (obj: D.Object);
    BEGIN
      IF (obj # NIL) THEN
        EXCL (obj. flags, D.objInSymbolFile);
        ClearImportedMods (obj. rightObj)
      END
    END ClearImportedMods;
  
  BEGIN
    (* get the magic number from the previous symbol file *)
    newSymbolFile := ~GetPreviousMagic (magicOld);
    
    (* determine file name and open file, but don't register before everything
       is done *)
    ParamPaths.GeneratePathExt (mod. name^, Config.symbolExtension, fileName);
    f := Files.Tmp (fileName, {Files.read, Files.write}, res);
    IF (f = NIL) THEN
      res. GetText (msg);
      E.FileError ("Couldn't create new symbol file `%'", fileName, msg)
    ELSE
      w := BinaryRider.ConnectWriter (f);
      (* write file header, leave empty space for magic id *)
      w. WriteBytes (symbolFileId, 0, 4);
      w. WriteLInt (0);
      WriteString (w, mod. name^);
      ClearImportedMods (Sym.importedMods);
      MarkExportedObjects (mod. localDecl);
      
      (* first write imported modules this file is depending on, then the rest
         of the modules *)
      importIndex := D.strRecord+1;
      WriteUsedImports;  
      WriteString (w, emptyString);
      WriteOtherImports (mod. localDecl);
      WriteString (w, emptyString);
      w. WriteNum (Config.symbolFileFormat);
      w. WriteNum (Config.symbolFileVersion);
      
      (* write flags and back-end specific module info *)
      WriteFlags (w, mod. flags * D.objExportMask);
      WriteFlags (w, mod. beFlags * StdTypes.objExportMaskBE);
      IF (D.objExportsBEInfo IN mod. flags) THEN
        SystemFlags.WriteObjectInfo (w, mod)
      END;
      
      objPos := w. Pos();
      structLen := 0;
      WriteTree (mod. localDecl);
      w. WriteNum (0);
      
      (* calculate magic number, insert it at position 4, 
         update the `used in symbol file' flags, and register file *)
      Fingerprint (f, objPos, magicId);
      w. SetPos (4);
      w. WriteLInt (magicId);
      mod. data(D.Const). int := magicId;
      
      (* compare new magic number with the one of the previous symbol file *)
      IF newSymbolFile THEN
        symbolFileChanged := FALSE
      ELSE
        symbolFileChanged := (magicId # magicOld)
      END;
      IF (w. res # BinaryRider.done) THEN
        w. res. GetText (msg);
        E.FileError ("Write error in file `%'", fileName, msg)
      END;
      f. Register;
      IF (f. res # Files.done) THEN
        f. res. GetText (msg);
        E.FileError ("Registering file `%' failed", fileName, msg)
      END;
      f .Close;
      IF (f. res # Files.done) THEN
        f. res. GetText (msg);
        E.FileError ("Closing file `%' failed", fileName, msg)
      END;
      
      (* cleanup struct markers *)
      FOR i := 0 TO structLen-1 DO
        structArray[i]. marker := -1;
        EXCL (structArray[i]. flags, D.structInSymbolFile);
        structArray[i] := NIL
      END
    END
  END Write;


PROCEDURE ReadFlags* (r: BinaryRider.Reader; VAR flags: SET);
  VAR
    i: LONGINT;
  BEGIN
    r. ReadNum (i);
    flags := SYSTEM.VAL (SET, i)
  END ReadFlags;

PROCEDURE Read* (moduleName: ARRAY OF CHAR; pos: LONGINT): D.Object;
(* Reads the symbol file of a given module.  If any errors occur, they are 
   reported with respect to file position `pos' and NIL is returned.  Otherwise
   the module and its exported symbol table is added to the list 
   `importedMods'.  Result is a copy of this module object, the copy's field
   `localTo' refers to the original object.  *)
  CONST
    noMode = MIN (LONGINT);
  TYPE
    ModuleList = POINTER TO ModuleListDesc;
    ModuleListDesc = RECORD
      next: ModuleList;
      mod: D.Object
    END;
  VAR
    f: Files.File;
    r: BinaryRider.Reader;
    mod, new, last: D.Object;
    fileName: Parameter.Filename;
    symId: ARRAY 16 OF CHAR;
    msg: ARRAY 256 OF CHAR;
    found: BOOLEAN;
    objMode, rest, i, fileFormat, fileVersion: LONGINT;
    modList: ModuleList;
    const: D.Const;
    res: Files.Result;
    
  PROCEDURE Abort;
    VAR
      msg: ARRAY 256 OF CHAR;
      num: ARRAY 32 OF CHAR;
    BEGIN
      msg := "Symbol file ";
      Strings.Append (fileName, msg);
      Strings.Append (" is corrupt, aborting at pos ", msg);
      IntStr.IntToStr (r. Pos(), num);
      Strings.Append (num, msg);
      Parameter.FatalError (msg)
    END Abort;
  
  PROCEDURE ReadObject (mode: LONGINT): D.Object;
    VAR
      obj: D.Object;
      name: D.String;
      valInt: LONGINT;
      valReal: LONGREAL;
      valSet: SET;
      
    PROCEDURE ReadStruct(): D.Struct;
      VAR
        form: LONGINT;
        typeName: D.String;
        obj: D.Object;
        t: D.Struct;
        modEntry: ModuleList;
        
      PROCEDURE ReadObjList (VAR obj: D.Object; parameter: BOOLEAN);
      (* Reads list of record fields or type-bound procedures.  *)
        VAR
          mode: LONGINT;
        BEGIN
          r. ReadNum (mode);
          IF (mode = 0) THEN
            obj := NIL
          ELSE
            obj := ReadObject (mode);
            obj. localTo := t;
            IF parameter THEN
              INCL (obj. flags, D.objIsParameter)
            END;
            ReadObjList (obj. rightObj, parameter)
          END
        END ReadObjList;
      
      BEGIN
        r. ReadNum (form);
        IF (form <= 0) THEN
          RETURN structArray[-form]
        ELSIF (form <= D.strNone) THEN
          RETURN D.struct[form]
        ELSE
          IF (form > D.strRecord) THEN  (* imported type *)
            typeName := ReadString (r);
            (* find module (it's already in memory) *)
            modEntry := modList;
            WHILE (form # D.strRecord+1) DO
              modEntry := modEntry. next;
              DEC (form)
            END;
            IF (modEntry = NIL) THEN Abort END;
            (* locate type declaration *)
            obj := Sym.FindDecl (modEntry. mod, typeName^);
            IF (obj = NIL) OR (obj. mode # D.objType) THEN Abort END;
            t := obj. type;
            AppendToStructArray (t)
          ELSE
            t := Sym.NewStruct (SHORT (SHORT (form)), D.undefPos);
            AppendToStructArray (t);
            ReadFlags (r, t. flags);
            ReadFlags (r, t. beFlags);
            
            t. base := ReadStruct();
            IF (t. form = D.strRecord) THEN
              IF (t. base. form = D.strNone) THEN
                t. base := NIL
              ELSE
                (* t. len := t. base. len+1;
                   note: can't set base here, because the base record's len
                   may not be set yet; therefore this is postponed to
                   StructAlloc *)
              END
            END;
            
            IF (D.structExportsBEInfo IN t. flags) THEN
              SystemFlags.ReadStructInfo (r, t)
            END;
            
            CASE t. form OF
            | D.strPointer, D.strOpenArray:
            | D.strProc, D.strRecord:
              ReadObjList (t. decl, t. form = D.strProc)
            | D.strArray:
              r. ReadNum (t. len)
            END
          END;
          RETURN t
        END
      END ReadStruct;
    
    BEGIN
      (* if the mode wasn't pre-read, do it now *)
      IF (mode = noMode) THEN
        r. ReadNum (mode)
      END;
      
      IF (mode = D.objRestParam) THEN 
        obj := Sym.NewObject ("...", D.objRestParam, D.undefPos);
        obj. type := D.struct[D.strNone];
        INCL (obj. flags, D.objIsParameter)
      ELSE
        IF (mode # -D.objType) & 
           ((mode < D.objUndef) OR (D.objTBProc < mode)) THEN
          Abort
        END;
        
        name := ReadString (r);
        obj := Sym.NewObject (name^, SHORT (SHORT (ABS (mode))), D.undefPos);
        obj. moduleId := mod. moduleId;
        ReadFlags (r, obj. flags);
        ReadFlags (r, obj. beFlags);
        obj. type := ReadStruct();
        IF (D.objExportsBEInfo IN obj. flags) THEN
          SystemFlags.ReadObjectInfo (r, obj)
        END;
        
        IF (mode = -D.objType) THEN
          obj. type. obj := obj          (* set type name *)
        ELSIF (mode = D.objConst) THEN   (* read constant's value *)
          CASE obj. type. form OF 
          | D.strBoolean..(D.strReal-1): 
            r. ReadNum (valInt);
            obj. data := D.GetIntConst (valInt, D.struct[obj. type. form])
          | D.strReal, D.strLongReal:
            r. ReadLReal (valReal);
            obj. data := D.GetRealConst (valReal, D.struct[obj. type. form])
          | D.strSet8..D.strSet64:
            r. ReadSet (valSet);
            obj. data := D.GetSetConst (valSet, D.struct[obj. type. form])
          | D.strStringConst8, D.strStringConst16:
            obj. data := ReadStringConst (r, obj. type. form)
          | D.strNil:  (* no value necessary *)
            obj. data := D.constNil
          END;
          obj. data(D.Const). preserve := TRUE
        ELSIF (mode = D.objTBProc) THEN    
          (* read procedure index and receiver *)
          r. ReadNum (obj. offset);
          obj. data := ReadObject (noMode)
        END;
        IF (mode = D.objProc) OR (mode = D.objTBProc) THEN
          Sym.MakeFormalParsLocal (obj)
        END
      END;
      RETURN obj
    END ReadObject;
  
  PROCEDURE ReadImportList (VAR list: D.Object; VAR modList: ModuleList);
    VAR
      str: D.String;
      magic: LONGINT;
    BEGIN
      str := ReadString (r);
      IF (str^ = "") THEN
        (* skip over list of modules whose types aren't used in the sym file *)
        LOOP
          str := ReadString (r);
          IF (str^ = "") THEN
            EXIT
          END;
          r. ReadLInt (magic);
        END;
        list := NIL
      ELSE
        r. ReadLInt (magic);
        list := Read (str^, pos);
        IF (list = NIL) THEN  
          (* failed to internalize symbol file; skip module *)
          ReadImportList (list, modList)
        ELSE
          IF(list. data(D.Const). int # magic) THEN
            E.ErrIns2 (pos, 302, moduleName, str^);
            (* $1 imports $2 with illegal key *)
          END;
          (* add module `list' to list of modules imported by the current
             module *)
          NEW (modList);
          modList. next := NIL;
          modList. mod := list;
          ReadImportList (list. rightObj, modList. next)
        END
      END
    END ReadImportList;
  
  PROCEDURE StructAlloc (t: D.Struct);
  (* Set size and alignment of type `t'.  *)
    VAR
      obj: D.Object;
    BEGIN
      IF (t # NIL) & (t. form # D.strNone) & (t. size = MIN (LONGINT)) THEN
        IF (t. form # D.strPointer) THEN
          (* before calling `StdTypes.StructAlloc', make sure that all types
             that are part of `t' have been allocated *)
          StructAlloc (t. base);
          
          IF (t. form = D.strRecord) THEN
            IF (t. base = NIL) THEN
              t. len := 0
            ELSE
              t. len := t. base. len+1
            END;
            
            obj := t. decl;
            WHILE (obj # NIL) DO
              StructAlloc (obj. type);
              obj := obj. rightObj
            END
          END
        END;
        StdTypes.StructAlloc (t)
      END
    END StructAlloc;
  
  BEGIN
    mod := FindImportedModule (moduleName);
    IF (mod = NIL) THEN  (* module isn't loaded, read its file *)
      (* find the symbol file using the redirection table *)
      found := ParamPaths.FindPathExt (moduleName, Config.symbolExtension, 
                                       FALSE, fileName);
      IF found THEN
        f := Files.Old (fileName, {Files.read}, res)
      END;
      
      IF ~found OR (f = NIL) THEN
        E.ErrIns (pos, 303, moduleName)  
        (* can't open/read symbol file of module *)
      ELSE  (* file exists, could be opened *)
        r := BinaryRider.ConnectReader (f);
        symId := "XXXX";
        r. ReadBytes (symId, 0, 4);
        IF (symId # symbolFileId) THEN
          E.ErrIns (pos, 304, fileName)  
          (* module's symbol file doesn't start with right key *)
          
        ELSE
          mod := Sym.NewModule (moduleName, pos);
          r. ReadLInt (mod. data(D.Const). int);
          
          mod. name := ReadString (r);
          IF (moduleName # mod. name^) THEN
            E.ErrIns2 (pos, -401, moduleName, mod. name^)
            (* warning: symbol file imported as $1 calls itself $2 *)
          END;
          
          (* add module to list of imported modules *)
          mod. moduleId := CreateModuleId();
          mod. level := Sym.globalLevel;
          mod. rightObj := Sym.importedMods;
          Sym.importedMods := mod;
          (* read list of imports and import the symbol tables of the modules 
             this one is depending on *)
          modList := NIL;
          ReadImportList (mod. leftObj, modList);
          r. ReadNum (fileFormat);
          r. ReadNum (fileVersion);
          IF (fileFormat # Config.symbolFileFormat) THEN
            IntStr.IntToStr (fileFormat, symId);
            E.ErrIns (pos, 308, symId)   (* invalid symbol file format *)
          ELSIF (fileVersion # Config.symbolFileVersion) THEN
            IntStr.IntToStr (fileVersion, symId);
            E.ErrIns (pos, 308, symId)   (* invalid symbol file format *)
          ELSE
          
            (* read back-end specific information *)
            ReadFlags (r, mod. flags);
            ReadFlags (r, mod. beFlags);
            IF (D.objExportsBEInfo IN mod. flags) THEN
              SystemFlags.ReadObjectInfo (r, mod)
            END;
            
            IF (r. res # BinaryRider.done) THEN
              E.ErrIns (pos, 305, fileName) (* unexpected end of symbol file *)
            END;
            last := NIL;
            structLen := 0;
            mod. localTo := Sym.currScope;  (* save top of scope stack *)
            Sym.OpenScope (mod, mod. moduleId, mod. level);
            r. ReadNum (objMode);
            WHILE (r. res = BinaryRider. done) & (objMode # 0) DO
              (* read next object, append it to list of declarations *)
              IF (last = NIL) THEN
                last := ReadObject (objMode);
                mod. localDecl := last
              ELSE
                last. rightObj := ReadObject (objMode);
                last := last. rightObj
              END;
              last. leftObj := NIL; last. rightObj := NIL; 
              last. localTo := mod; last. moduleId := mod. moduleId;
              last. level := mod. level;
              IF (r. res # BinaryRider. done) THEN
                E.ErrIns (pos, 305, fileName) (* unexpected end of symbol file *)
              END;
              r. ReadNum (objMode)
            END;
            
            (* make sure that no more bytes follow *)
            rest := f. Length() - r. Pos();
            IF (rest # 0) THEN
              IntStr.IntToStr (rest, symId);
              E.ErrIns2 (pos, -402, symId, fileName)
              (* warning: ignoring last $1 bytes of $2 *)
            END
          END;
          Sym.CloseScope (FALSE);        (* restores scope stack *)
          Sym.BalanceTree (mod);         (* convert list into tree *)
          
          (* set size and alignment of types, cleanup structure table *)
          FOR i := 0 TO structLen-1 DO
            StructAlloc (structArray[i]);
            structArray[i] := NIL
          END
        END;
        IF (r. res # BinaryRider.done) THEN
          r. res. GetText (msg);
          E.FileError ("Read error in file `%'", fileName, msg)
        END;
        f. Close
      END
    END;
    
    (* if the module is loaded, return a copy of it *)
    IF (mod # NIL) THEN
      NEW (new);
      new^ := mod^;
      new. pos := pos;
      NEW (const);
      const^ := new. data(D.Const)^;
      const. string := new. name;
      new. data := const;
      RETURN new
    ELSE
      RETURN NIL
    END
  END Read;

BEGIN
  NEW (structArray, firstArray);
  symbolFileId[0] := CHR (ORD ("o")+128);
  symbolFileId[1] := CHR (ORD ("o")+43);
  symbolFileId[2] := CHR (ORD ("c")-17);
  symbolFileId[3] := CHR (ORD ("s"));
  symbolFileId[4] := 0X;
  emptyString := "";
  NEW (emptyStringPtr, 2);
  COPY ("", emptyStringPtr^)
END SymbolFile.
