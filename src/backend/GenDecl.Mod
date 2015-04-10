(* 	$Id: GenDecl.Mod,v 1.51 2001/01/14 14:10:54 ooc-devel Exp $	 *)
MODULE GenDecl;
(*  Handles name mangling, generates C declarations and type casts.
    Copyright (C) 1996-2001  Michael van Acken

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
  TextRider, Str := Strings, IntStr, D := Data, StdTypes, StdPragmas, Scanner,
  Sym := SymbolTable, SymbolFile, SystemFlags, Classify, A := Allocate, 
  GenInclude, GenConst;
  
  
VAR
  anonCounter: INTEGER;  (* used to build names for anonymous types *)
  nameCounter: INTEGER;  (* used to build variables for strings *)
  recordCounter: INTEGER;(* used to build variables for tb proc lists *)
  ptrListCounter: INTEGER;(* used to build variables for pointer lists *)
  dummyName: D.String;
  
VAR
  rwList: ARRAY 256, 10 OF CHAR;  (* hash table with reserved C words *)

  
TYPE
  ObjectList* = POINTER TO ARRAY OF D.Object;

VAR
  objList-: ObjectList;
  objCount-: LONGINT;    (* indices [0..objCount-1] used in objList *)
  typeObject: D.Object;  (* used in `TypeDeclaration' *)
  beInfo: SystemFlags.Info;  (* used in `VarDeclaration' *)
  currModule: INTEGER;   (* id of module that is currently translated *)
  
CONST  (* flags for the `dmode' parameter of Declaration and TypeDeclaration *)
  function* = 1;                          
  (* marks a function declaration; setting this prevents Declaration from 
     adding an additional pointer level around the declaration name (which is 
     necessary for declarations of function types and function variables) *)
  prototype* = 2;
  (* end function declaration with a semicolon, ie write a function prototype
     (instead of a function definition or a function variable) *)
  external* = 3;
  (* tells Declaration to put `extern' before the declaration *)
  static* = 4;
  (* tells Declaration to put `static' before the declaration *)
  typeExpression* = 5;
  (* this suppresses the name of the declaration, reducing the whole 
     declaration to a type expression that can be used for a type cast *)
  formalParam* = 6;
  (* the declaration describes a function's formal parameter; for values that
     are passed per reference an additional pointer level is introduced *)
  sideEffectParam* = 7;
  (* writing parameter declaration for a nonlocal side-effect, i.e. a parameter
     that is use for reading or writing a variable or parameter of an enclosing
     procedure *)
  sideEffectReference* = 8;
  (* the side-effect parameter is implemented as a reference to the actual 
     value, allowing read and write access; if this flag isn't set then the
     nonlocal variable isn't modified by the procedure and the variable's value
     is passed to the procedure (if possible) *)
  doNotMark* = 9;
  (* don't mark an object with `objEmitted' after its declaration is written;
     this flag is set for record fields (they may appear again when writing the
     extensions of the current type) and for formal parameters (they appear 
     both in the procedure's declaration and definition) *)
  ignoreMark* = 10;
  (* even if the object is marked as emitted, write declaration again; this is
     used to force output of nonlocal variable parameters that model side-
     effects of nested procedures *)
  ignoreUsedDecl* = 11;
  (* when writing the declaration, assume that all names appearing in it are
     already correctly defined *)
  ignoreOtherModule* = 12;
  (* normally Declaration won't write anything if the object in question is
     defined in another module; setting this flag overides this *)
  referenceName = 13;
  (* the name of the declaration will be suffixed by `__ref'; used for names of
     value parameters that are copied into local variables later on *) 
  functionPointer = 14;
  (* add an additional pointer level to the function type *)
  noSemicolon* = 15;
  (* don't terminate the declaration with a semicolon, leave it to the calling
     procedure to finish the job *)
  noSpace = 16;
  (* for `DeclarationName': if set, omit space character before name *)


TYPE
  (* used by EnumerateSideEffects to iterate over the side-effects of a nested
     procedure: *)
  SideEffectInfo* = RECORD  
    opnd: D.Opnd;
    result: D.Result;
    exit, enter: D.Instruction;
    
    obj-: D.Object;    (* nonlocal variable or parameter being accessed *)
    attrib-: INTEGER;  (* one of the Data.symLocXXX values *)
    passPerReference-: BOOLEAN;  (* use pointer instead of value *)
    
    continue-: BOOLEAN;
  END;


VAR
  tbCallList*: ObjectList;
  (* holds list of type-bound procedures whose index value isn't known at
     the point of their declaration *)


PROCEDURE IllegalName (VAR str: ARRAY OF CHAR): BOOLEAN;
(* If `str' is a legal C identifier (ie if it is a reserved word), or if 
   `str' appears in the list of forbidden identifiers (like malloc), then 
   return TRUE.  Note that such a name can only be used for identifiers with 
   local binding, which includes parameters and struct fields, since all the
   other identifiers contains an underscore.  *)
  VAR
    i: INTEGER;
    hash: LONGINT;
  BEGIN
    hash := 0; i := 0;
    WHILE (str[i] # 0X) DO
      IF (str[0] < "a") OR (str[0] > "z") THEN
        RETURN FALSE
      END;
      INC (hash, LONG (ORD (str[i])));
      INC (i)
    END;
    hash := hash MOD 256;

    IF (rwList[hash, 0] # 0X) &
       ((rwList[hash] = str) OR (hash # 255) & (rwList[hash+1] = str)) THEN
      RETURN TRUE
    ELSE
      (* check whether `str' clashes with a name that can be assigned by the 
         allocator to a value  *)
      CASE str[0] OF
      | Classify.prefixInt, Classify.prefixHuge, Classify.prefixReal,
        Classify.prefixLongReal, Classify.prefixAuxiliary:
        i := 1;
        WHILE ("0" <= str[i]) & (str[i] <= "9") DO
          INC (i)
        END;
        RETURN (i >= 2) & (str[i] = 0X)
      ELSE
        RETURN FALSE
      END
    END
  END IllegalName;

PROCEDURE AssignNames* (block: D.Object);
(* Assigns info blocks and C names to all declarations and types in `block'. 
   The names are choosen in such a way that they do not match one of the 
   identifiers in `rwList' and that all global identifiers are prefixed by the
   module name.  *)
  VAR
    str: ARRAY 1024 OF CHAR;

  PROCEDURE SetObjectName (obj: D.Object);
  (* Allocates C name for `obj' and all unnamed structured types that are part
     of it.  This procedure considers formal parameter of procedures, but
     it doesn't deal with a procedure's local declarations.  *)
    VAR
      type: D.Struct;
      i: INTEGER;
      l: D.Object;
    
    PROCEDURE BuildName (VAR s0: ARRAY OF CHAR; 
                         s1, s2: ARRAY OF CHAR): D.String;
    (* Appends `s0', `s1', and `s2' and places the result on the heap.  *)
      VAR
        ptr: D.String;
        str: ARRAY 4*1024 OF CHAR;
        i, j: INTEGER;
      BEGIN
        i := 0;
        WHILE (s0[i] # 0X) DO
          str[i] := s0[i]; INC (i)
        END;
        j := 0;
        WHILE (s1[j] # 0X) DO
          str[i] := s1[j]; INC (i); INC (j)
        END;
        j := 0;
        WHILE (s2[j] # 0X) DO
          str[i] := s2[j]; INC (i); INC (j)
        END;
        str[i] := 0X;
        NEW (ptr, i+1);
        COPY (str, ptr^);
        RETURN ptr
      END BuildName;
    
    PROCEDURE SetStructName (t: D.Struct);
    (* Allocates C name for `t'.  *)
      VAR
        str: ARRAY 64 OF CHAR;
    
      PROCEDURE AssignList (list: D.Object);
        BEGIN  (* handles list of record fields and formal parameters *)
          IF (list # NIL) THEN
            IF (list. mode = D.objTBProc) THEN
              AssignNames (list)
            ELSE
              SetObjectName (list)
            END;
            AssignList (list. rightObj)
          END
        END AssignList;
      
      BEGIN
        IF ~(StdTypes.structNamed IN t. beFlags) THEN
          (* enter this code just once for every type; a simple test for 
             `beInfo.name=NIL' is insufficient, since names for imported 
             unnamed records already exist before this procedure is run *)
          SystemFlags.CreateInfo (t);
          INCL (t. beFlags, StdTypes.structNamed);
          
          IF (t. beInfo(SystemFlags.Info). name = NIL)  THEN
            IF (t. form <= D.strNone) THEN
              (* predefined type, get the corresponding C type expression *)
              StdTypes.BasicTypes (t. form, str);
              t. beInfo(SystemFlags.Info). name := BuildName (str, "", "")
            ELSIF (t. obj = NIL) THEN
              (* this type isn't associated with an Oberon-2 name; create a 
                 name that can't clash with a legal O2 name *)
              IF Sym.TypeInGroup (t, D.grpArray) OR (t. form = D.strPointer) OR
                 (t. form = D.strProc) THEN
                (* no need to assign names to arrays, pointer, or procedures,
                   since their structure is always part of the type 
                   expression *)
                t. beInfo(SystemFlags.Info). name := dummyName
              ELSE
                IntStr.IntToStr (anonCounter, str);  (* part of unique name *)
                INC (anonCounter);
                t. beInfo(SystemFlags.Info). name := 
                   BuildName (block. beInfo(SystemFlags.Info). name^, "_", str)
              END
            ELSIF (t. obj. mode = D.objType) THEN
              (* reuse name of the type declaration *)
              SetObjectName (t. obj);
              t. beInfo(SystemFlags.Info). name := 
                                         t. obj. beInfo(SystemFlags.Info). name
            END
          END;
          
          IF (t. base # NIL) THEN
            (* deal with pointer base type, element type, etc *)
            SetStructName (t. base)
          END;
          IF (t. form = D.strProc) OR (t. form = D.strRecord) THEN
            (* assign names to formal parameters resp. record fields *)
            AssignList (t. decl)
          END
        END
      END SetStructName;
    
    PROCEDURE FromInterfaceModule (obj: D.Object): BOOLEAN;
      VAR
        mod: D.Object;
      BEGIN
        mod := Sym.Module (obj);
        RETURN (StdTypes.objInterfaceModule IN mod. beFlags)
      END FromInterfaceModule;
    
    PROCEDURE NameClash (name: D.String; struct: D.Struct): BOOLEAN;
    (* Returns TRUE if a field `name' is defined in `struct' or one of its base
       types, regardless if the field is visible in the current module or 
       not.  *)
      VAR
        old: D.Object;
      BEGIN
        IF (struct = NIL) THEN
          RETURN FALSE
        ELSE
          old := NIL;
          WHILE (struct # NIL) & (old = NIL) DO
            old := Sym.FindDecl (struct, name^);
            struct := struct. base
          END;
          RETURN (old # NIL) & (old. mode = D.objField)
        END
      END NameClash;
    
    BEGIN
      IF ((obj. beInfo = NIL) OR (obj. beInfo(SystemFlags.Info). name = NIL)) &
         ((obj. mode # D.objModule) OR (obj = block)) THEN
        (* enter this code just once for every object *)
        SystemFlags.CreateInfo (obj);
        IF (obj. mode = D.objType) THEN
          AssignNames (obj. localTo(D.Object))
        END;
        
        (* generate a (hopefully unique) C name for the object *)
        IF (StdTypes.objFixedName IN obj. beFlags) THEN
          obj. beInfo(SystemFlags.Info). name := 
                                   obj. beInfo(SystemFlags.Info). givenName
        ELSIF (obj. mode = D.objModule) THEN
          (* name for module: replace all name part separators with "_" *)
          obj. beInfo(SystemFlags.Info). name := BuildName (obj. name^, "","");
          i := 0;
          WHILE (obj. beInfo(SystemFlags.Info). name[i] # 0X) DO
            IF (obj. beInfo(SystemFlags.Info). name[i] = 
                Scanner.moduleSeparator) THEN
              obj. beInfo(SystemFlags.Info). name[i] := "_"
            END;
            INC (i)
          END
          
        ELSIF (D.objIsParameter IN obj. flags) OR (obj. mode = D.objField) OR
              (obj. mode = D.objVar) & (obj. level > Sym.globalLevel) THEN
          (* the name of a record field, a variable, or a formal parameter is
             used for the C name, although it may need some twisting to avoid
             names like int, for, malloc, etc *)
          IF (obj. mode = D.objField) & 
             NameClash (obj. name, obj. localTo(D.Struct). base) THEN
            (* field with same name already exists in base type; add extension
               level of record to get a unique identifier *)
            IntStr.IntToStr (obj. localTo(D.Struct). len, str);
            obj. beInfo(SystemFlags.Info). name := BuildName (obj. name^, "_", str)
          ELSE
            IF IllegalName (obj. name^) THEN
              obj. beInfo(SystemFlags.Info). name  := BuildName (obj. name^, "_", "")
            ELSE
              obj. beInfo(SystemFlags.Info). name := obj. name
            END
          END
        ELSIF (obj. mode = D.objTBProc) THEN
          (* the name of a type-bound procedure is prefixed by its receiver's
             type name *)
          type := obj. data(D.Object). type;
          IF (type. form = D.strPointer) THEN
            type := type. base
          END;
          SetStructName (type);
          obj. beInfo(SystemFlags.Info). name := 
             BuildName (type. beInfo(SystemFlags.Info). name^, "_", obj. name^)
        ELSIF FromInterfaceModule (obj) & (obj. level = Sym.globalLevel) &
              (obj. mode IN {D.objVar, D.objProc}) THEN
          obj. beInfo(SystemFlags.Info). name := obj. name
        ELSE
          (* all other identifiers are prefixed by the module name and the
             name of the enclosing procedure(s) *)
          l := obj. localTo(D.Object);
          IF (l. mode = D.objModule) THEN
            obj. beInfo(SystemFlags.Info). name := 
              BuildName (l. beInfo(SystemFlags.Info). name^, "__", obj. name^)
          ELSE
            obj. beInfo(SystemFlags.Info). name := 
              BuildName (l. beInfo(SystemFlags.Info). name^, "_", obj. name^)
          END
        END;
        
        IF (obj. type # NIL) THEN
          (* assign name to variable type, formal parameters, etc *)
          SetStructName (obj. type)
        END;
        IF (obj. mode = D.objTBProc) THEN  
          (* assign name to receiver of type-bound procedure *)
          SetObjectName (obj. data(D.Object))
        END
      ELSE
        (* make sure that the formal parameters are handled correctly if
           `obj' resolves a procedure forward declaration *)
        IF (obj. mode = D.objTBProc) THEN  
          (* assign name to receiver of type-bound procedure *)
          SetObjectName (obj. data(D.Object));
          SetStructName (obj. type)
        ELSIF (obj. mode = D.objProc) THEN  
          SetStructName (obj. type)
        END
      END
    END SetObjectName;
  
  PROCEDURE TraverseTree (obj: D.Object);
  (* Traverses all declarations in binary tree with root `obj' and assigns them
     their names.  *)
    BEGIN
      IF (obj # NIL) THEN
        TraverseTree (obj. leftObj);
        IF (obj. mode = D.objProc) THEN
          AssignNames (obj)
        ELSE
          SetObjectName (obj)
        END;
        TraverseTree (obj. rightObj)
      END
    END TraverseTree;
  
  PROCEDURE AssignImports (obj: D.Object);
    BEGIN
      IF (obj # NIL) THEN
        AssignImports (obj. leftObj);
        IF (obj. mode = D.objModule) THEN
          AssignNames (SymbolFile.FindImportedModule (obj. data(D.Const). string^))
        END;
        AssignImports (obj. rightObj)
      END
    END AssignImports;
  
  BEGIN
    IF ~(D.objIsInitialized IN block. flags) &
       ((block. beInfo = NIL) OR 
        (block. beInfo(SystemFlags.Info). name = NIL) OR
        (D.objWasForwardDecl IN block. flags)) THEN
      INCL (block. flags, D.objIsInitialized);
      IF (block. mode = D.objModule) THEN
        (* make sure that declarations in imported modules have their names 
           set *)
        AssignImports (block. localDecl);
        
        anonCounter := 0;
        nameCounter := 0;
        recordCounter := 0;
        ptrListCounter := 0;
      ELSIF (block. mode # D.objTBProc) THEN
        (* make sure that declarations in enclosing scopes have their names 
           set *)
        AssignNames (block. localTo(D.Object))
      END;

      SetObjectName (block);
      (* first handle all declarations in `block' to make sure that all types
         that might be referenced nonlocally are assigned a name; procedures 
         are ignored in this pass *)
      TraverseTree (block. localDecl);
      
      EXCL (block. flags, D.objIsInitialized)
    END
  END AssignNames;


PROCEDURE EnumerateSideEffects* (proc: D.Object; VAR einfo: SideEffectInfo);
  VAR
    opnd: D.Opnd;
    result: D.Result;
    loc: D.SymLocation;
  BEGIN
    IF (proc # NIL) THEN  (* initialize einfo *)
      einfo. enter := proc. greg. EnterInstr();
      einfo. exit := proc. greg. ExitInstr();
      
      (* find first result that isn't part of the formal parameter list *)
      result := einfo. enter. nextResult;
      loc := A.GetLocation (result);
      WHILE (result # NIL) & 
            ((loc. var IS D.Struct) OR (loc. var(D.Object). localTo = proc)) DO
        result := result. nextResult;
        loc := A.GetLocation (result)
      END;
      IF (einfo. exit # NIL) THEN
        opnd := einfo. exit. opndList
      ELSE
        opnd := NIL
      END;
      einfo. continue := TRUE
      
    ELSE  (* move opnd or result one step forward *)
      result := einfo. result;
      opnd := einfo. opnd;
      IF (result # NIL) THEN
        result := result. nextResult
      ELSE
        opnd := opnd. nextOpnd
      END
    END;
    
    (* if opnd (resp. result) doesn't refer to a side-effect input or output,
       or this particular value has already been dealt with, then move opnd 
       (resp. result) forward until such a value is reached *)
    loc := A.GetLocation (result);
    WHILE (result # NIL) & 
          ((loc. var IS D.Struct) OR
           (loc. var(D.Object). name[0] = "$") OR
           (loc. var(D.Object). localTo = proc) OR
           (loc. var(D.Object). level = Sym.globalLevel)) DO
      result := result. nextResult;
      loc := A.GetLocation (result)
    END;
    IF (result = NIL) THEN
      loc := A.GetLocation (opnd);
      WHILE (opnd # NIL) &
            ((loc. var IS D.Struct) OR
             (loc. var(D.Object). name[0] = "$") OR
             (loc. var(D.Object). level = Sym.globalLevel) OR
             (A.FindResult (einfo. enter, loc. var, loc. attrib) # NIL)) DO
        opnd := opnd. nextOpnd;
        loc := A.GetLocation (opnd)
      END
    END;
    
    IF (result # NIL) OR (opnd # NIL) THEN
      einfo. result := result;
      einfo. opnd := opnd;
      einfo. obj := loc. var(D.Object);
      einfo. attrib := loc. attrib;
      
      (* the side-effect parameter is passed per reference if
          - a value of its type is never passed as value parameter, or
          - its value is changed in the procedure (ie it appears as operand of
            the exit instruction, or
          - $mem appears as argument of the exit instruction *)
      einfo. passPerReference := 
        (einfo. attrib = D.symLocObject) & 
        (StdTypes.PassPerReference (einfo. obj, TRUE) OR
         (A.FindResult (einfo. enter, einfo. obj, D.symLocAddress) # NIL) OR
         (A.FindOperand (einfo. exit, einfo. obj, D.symLocObject) # NIL) OR
         (A.FindOperand (einfo. exit, Sym.mem, D.symLocObject) # NIL));
      
      (* skip any address operands whose object is passed per reference *)
      IF (einfo. attrib = D.symLocAddress) &
         ((A.FindResult (einfo. enter, einfo. obj, D.symLocObject) # NIL) OR
          (A.FindOperand (einfo. exit, einfo. obj, D.symLocObject) # NIL)) THEN
        EnumerateSideEffects (NIL, einfo)
      END
    ELSE  (* all operands and results scanned, abort iteration *)
      einfo. continue := FALSE
    END
  END EnumerateSideEffects;



PROCEDURE NewLine* (w: TextRider.Writer; off: INTEGER);
(* Iff off>=0 print `newline' and indent for `off' levels.  *)
  BEGIN
    IF (off >= 0) THEN
      w. WriteLn;
      WHILE (off > 0) DO
        w. WriteString ("  ");
        DEC (off)
      END
    END
  END NewLine;

PROCEDURE ArrayLength (w: TextRider.Writer; par: D.Object; dim: INTEGER; 
                       declaration, nonlocal: BOOLEAN);
(* Writes parameter declaration of length of formal parameter `par' in 
   dimension `dim' if `declaration' is `TRUE'.  For `declaration=FALSE' it'll
   simply write the name that refers to the specified dimension.  *)
  VAR
    str: ARRAY 64 OF CHAR;
  BEGIN
    IF declaration THEN
      StdTypes.BasicTypes (D.strLongInt, str);
      w. WriteString (str);
      w. WriteChar (" ")
    END;
    IF nonlocal THEN
      w. WriteString (par. localTo. beInfo(SystemFlags.Info). name^);
      w. WriteChar ("_")
    END;
    w. WriteString (par. beInfo(SystemFlags.Info). name^);
    w. WriteChar ("_");
    (* make sure that such a name will never clash with a name assigned to 
       an unnamed structured type (they look like "Module_Number", eg "M_0") *)
    w. WriteInt (dim, 0); w. WriteChar ("d")
  END ArrayLength;

PROCEDURE TypeTag (w: TextRider.Writer; par: D.Object; 
                   declaration, nonlocal: BOOLEAN);
(* Writes parameter declaration for type tag of formal parameter `par' if 
   `declaration' is `TRUE'.  For `declaration=FALSE' it'll simply write the 
   name that refers to the specified type tag.
   pre: (par. declaration = D.objVarPar) & (par. type. form = D.strRecord) & 
        ~(objNoTypeTag IN par. flags) *)
  BEGIN
    IF declaration THEN
      w. WriteString ("_Type ")
    END;
    IF nonlocal THEN
      w. WriteString (par. localTo. beInfo(SystemFlags.Info). name^);
      w. WriteChar ("_")
    END;
    w. WriteString (par. beInfo(SystemFlags.Info). name^);
    w. WriteString ("__tag")
  END TypeTag;



PROCEDURE ^ TypeDeclaration* (w: TextRider.Writer; t: D.Struct; 
                              dmode: SET; off: INTEGER);
                             
PROCEDURE Declaration* (w: TextRider.Writer; obj: D.Object; 
                        dmode: SET; off: INTEGER);
  VAR
    noDefinition: BOOLEAN;
                      
  PROCEDURE EmitUsedDeclarations (type: D.Struct);
    VAR
      t: D.Struct;
    
    PROCEDURE WriteDeclaration (type: D.Struct);
      BEGIN
        IF (type. obj = NIL) THEN
          EmitUsedDeclarations (type)
        ELSE
          TypeDeclaration (w, type, {}, off)
        END
      END WriteDeclaration;
    
    PROCEDURE WriteList (obj: D.Object);
      BEGIN
        WHILE (obj # NIL) DO
          IF (obj. mode # D.objTBProc) THEN
            WriteDeclaration (obj. type)
          END;
          obj := obj. rightObj
        END
      END WriteList;
  
    BEGIN
      IF (type. obj # NIL) & (type. obj. moduleId # currModule) THEN
        TypeDeclaration (w, type, {}, off)
      ELSE
        IF (type. form = D.strRecord) THEN
          (* make sure that we can define the fields of `type' and all fields
             inherited from its base type *)
          t := type;
          WHILE (t # NIL) DO
            WriteList (t. decl);
            IF (t # type) & (t. obj # NIL) THEN
              (* the header file containing the base type has to be included
                 since it might be used later to define the type descriptor of
                 `type' *)
              TypeDeclaration (w, t, {}, off)
            END;
            t := t. base
          END
        ELSIF (type. form = D.strProc) THEN
          WriteList (type. decl)
        END;
        IF (type. form = D.strArray) OR (type. form = D.strOpenArray) OR
           (type. form = D.strProc) OR (type. form = D.strPointer) THEN
          WriteDeclaration (type. base)
        ELSIF (type. form = D.strRecord) & (type. obj = NIL) THEN
          (* make sure that a unnamed record type is properly defined in its
             own typedef statement prior to its use *)
          TypeDeclaration (w, type, {}, off)
        END
      END
    END EmitUsedDeclarations;
  
  PROCEDURE CanUseTypeName (t: D.Struct; dmode: SET): BOOLEAN;
  (* The typedef name associated with `t' can be used if such a name is set and
     `t' is already defined, i.e. if it has already been declared in the 
     current module, is an imported type, is a predefined type, or is an 
     unnamed record type defined previously.  To avoid problems with types 
     defined in procedures and accessed again in nested procedures, nonglobal 
     (but not struct) types are never referenced by name.  *)
    BEGIN
      RETURN (t. beInfo # NIL) & 
             (t. beInfo(SystemFlags.Info). name # NIL) &
             (t. beInfo(SystemFlags.Info). name # dummyName) &
             ((t. form <= D.strNone) OR
              (t. obj = NIL) & (t. form = D.strRecord) & 
                ~(typeExpression IN dmode) OR
              (StdTypes.structEmitted IN t. beFlags) OR
              (t. obj # NIL) & 
               ((t. obj. moduleId # currModule) & 
                  ((t. form = D.strRecord) OR
                   (D.objIsExported IN t. obj. flags)) OR 
                (t. obj. moduleId = currModule) & 
                  (ignoreUsedDecl IN dmode))) &
             ~((typeExpression IN dmode) & (t. form = D.strArray)) &
             ((t. obj = NIL) OR (t. obj. level = Sym.globalLevel) OR
              (t. form = D.strRecord))
    END CanUseTypeName;
  
  PROCEDURE ArrayBase (t: D.Struct; VAR size: LONGINT): D.Struct;
    VAR
      base: D.Struct;
      open: BOOLEAN;
    BEGIN
      base := t; open := FALSE; size := 1;
      REPEAT
        IF (base. form = D.strOpenArray) THEN
          size := 0; open := TRUE
        ELSE
          size := size*base. len
        END;
        base := base. base
      UNTIL ~Sym.TypeInGroup (base, D.grpArray);
      IF open THEN
        size := -1
      END;
      IF (base. form = D.strPointer) & (base. base = t) THEN
        base := D.struct[D.strPtr]
      END;
      RETURN base
    END ArrayBase;
  
  PROCEDURE Pointer (left: BOOLEAN; base: D.Struct);
    VAR
      paren: BOOLEAN;
      arrayBase: D.Struct;
      size: LONGINT;
    BEGIN
      IF Sym.TypeInGroup (base, D.grpArray) THEN
        arrayBase := ArrayBase (base, size)
      ELSE
        size := 0
      END;
      IF (size >= 0) THEN
        paren := (base. form = D.strArray) OR (base. form = D.strProc) OR
                 (base. form = D.strOpenArray);
        IF left THEN
          IF paren THEN
            w. WriteChar ("(")
          END;
          w. WriteChar ("*")
        ELSIF paren THEN
          w. WriteChar (")")
        END
      END
    END Pointer;
  
  PROCEDURE LeftTypeExpr (t: D.Struct; dmode: SET);
    VAR
      base: D.Struct;
      size: LONGINT;
      dmode0: SET;
      
    PROCEDURE PadStruct (from, upto: LONGINT);
      VAR
        i: LONGINT;
      BEGIN
        IF (from < upto) THEN
          NewLine (w, off+1);
          w. WriteString ("char ");
          FOR i := from TO upto-1 DO
            IF (i > from) THEN
              w. WriteString (", ")
            END;
            w. WriteChar ("_");
            w. WriteLInt (i, 0);
            w. WriteString ("pad")
          END;
          w. WriteChar (";")
        END
      END PadStruct;
    
    PROCEDURE EmitFields (t: D.Struct; base: BOOLEAN): LONGINT;
      VAR
        end: LONGINT;
        field: D.Object;
      BEGIN
        IF (t # NIL) THEN
          end := EmitFields (t. base, TRUE);
          
          field := t. decl;
          WHILE (field # NIL) DO
            IF (field. mode = D.objField) THEN  
              (* write single record field *)
              PadStruct (end, field. offset);
              Declaration (w, field, {doNotMark, ignoreMark, ignoreOtherModule}, off+1);
              end := field. offset+field. type. size
            END;
            field := field. rightObj
          END;
          
          IF (end = 0) & ~base THEN 
            (* avoid declaration of empty struct: insert dummy field *)
            NewLine (w, off+1);
            w. WriteString ("char _dummy;")
          END;
          
          RETURN end
        ELSE
          RETURN 0
        END
      END EmitFields;
    
    BEGIN
      IF (t # NIL) THEN
        IF CanUseTypeName (t, dmode) THEN
          w. WriteString (t. beInfo(SystemFlags.Info). name^);
          IF (functionPointer IN dmode) THEN
            w. WriteChar ("*")
          END
        ELSE
          dmode0 := dmode-{function, functionPointer, typeExpression};
          CASE t. form OF
          | D.strPtr:  
            (* necessary to handle this case here if D.strPtr is used without 
               importing SYSTEM, e.g. for pathological arrays *)
            w. WriteString ("void*")
          | D.strPointer:
            IF (t. base. form = D.strRecord) THEN
              IF (D.structUnion IN t. base. flags) THEN
                w. WriteString ("union ")
              ELSE
                w. WriteString ("struct ")
              END;
              w. WriteString (t. base. beInfo(SystemFlags.Info). name^)
            ELSE
              LeftTypeExpr (t. base, dmode0)
            END;
            Pointer (TRUE, t. base)
          | D.strProc:
            LeftTypeExpr (t. base, dmode0);
            IF ~(function IN dmode) THEN
              Pointer (TRUE, t)
            END;
            IF (functionPointer IN dmode) THEN
              w. WriteChar ("*")
            END
          | D.strArray, D.strOpenArray:
            base := ArrayBase (t, size);
            LeftTypeExpr (base, dmode0);
            IF (size < 0) OR (typeExpression IN dmode) THEN
              Pointer (TRUE, base)
            END
          | D.strRecord:
            IF (D.structUnion IN t. flags) THEN
              w. WriteString ("union ")
            ELSE
              w. WriteString ("struct ")
            END;
            w. WriteString (t. beInfo(SystemFlags.Info). name^);
            w. WriteString (" {");
            PadStruct (EmitFields (t, FALSE), t. size);
            NewLine (w, off);
            IF (t. beFlags*{StdTypes.structAlign1..StdTypes.structAlign8} # {}) THEN
              w. WriteString ("} _NOALIGN")
            ELSE
              w. WriteString ("}")
            END
          END
        END
      END
    END LeftTypeExpr;
  
  PROCEDURE DeclarationName (obj: D.Object; dmode: SET);
    PROCEDURE Name (obj: D.Object);
      BEGIN
        IF (sideEffectParam IN dmode) THEN
          w. WriteString (obj. localTo(D.Object). beInfo(SystemFlags.Info). name^);
          w. WriteChar ("_")
        END;
        w. WriteString (obj. beInfo(SystemFlags.Info). name^);
        IF (referenceName IN dmode) THEN
          w. WriteString ("__ref")
        END
      END Name;
    
    BEGIN
      IF ~Sym.TypeInGroup (obj. type, D.grpArray) & 
         ((formalParam IN dmode) & StdTypes.PassPerReference (obj, TRUE) OR
          (sideEffectReference IN dmode)) THEN
        IF ~(noSpace IN dmode) THEN
          w. WriteChar (" ")
        END;
        Pointer (TRUE, obj. type);
        IF ~(typeExpression IN dmode) THEN
          Name (obj)
        END;
        Pointer (FALSE, obj. type)
      ELSIF ~(typeExpression IN dmode) THEN
        IF ~(noSpace IN dmode) THEN
          w. WriteChar (" ")
        END;
        Name (obj)
      END
    END DeclarationName;
  
  PROCEDURE FormalPars (t: D.Struct);
    VAR
      par: D.Object;
      writeSep: BOOLEAN;
      einfo: SideEffectInfo;
      declFlags: SET;
    
    PROCEDURE WriteSep;
      BEGIN
        IF writeSep THEN
          w. WriteString (", ")
        ELSE
          writeSep := TRUE
        END
      END WriteSep;
    
    PROCEDURE WriteParam (par: D.Object);
      VAR
        t: D.Struct;
        i: INTEGER;
        fmode: SET;
      BEGIN
        WriteSep;
        t := par. type;
        IF (par. mode = D.objRestParam) THEN
          w. WriteString ("...")
        ELSE
          fmode := {formalParam, doNotMark, ignoreOtherModule, ignoreMark}+
                   dmode*{ignoreUsedDecl, typeExpression};
          IF (StdTypes.objLocalCopy IN par. beFlags) THEN
            INCL (fmode, referenceName)
          END;
          Declaration (w, par, fmode, off)
        END;
        
        (* add parameters for array length and type tag *)
        IF Sym.TypeInGroup (t, D.grpArray) &
           ~(D.objNoLengthTag IN par. flags) THEN
          FOR i := 0 TO t. OpenDimensions()-1 DO
            WriteSep;
            ArrayLength (w, par, i, TRUE, FALSE)
          END
        ELSIF (par. mode = D.objVarPar) & (t. form = D.strRecord) &
              ~(D.objNoTypeTag IN par. flags) THEN
          WriteSep;
          TypeTag (w, par, TRUE, FALSE)
        END
      END WriteParam;
    
    BEGIN
      writeSep := FALSE;
      w. WriteString ("(");
      
      IF (obj. mode = D.objTBProc) THEN  (* emit receiver *)
        WriteParam (obj. data(D.Object))
      END;
      (* write out standard parameters *)
      par := t. decl;
      WHILE (par # NIL) DO
        WriteParam (par);
        par := par. rightObj
      END;
      
      IF (obj. mode = D.objProc) & (obj. level > Sym.globalLevel) THEN  
        (* nested procedure, add nonlocal (but not global) variables as 
           reference parameters, and type tags resp. array lengths as value 
           parameters to the formal parameter list *)
        EnumerateSideEffects (obj, einfo);
        WHILE einfo. continue DO
          WriteSep;
          IF (einfo. attrib = D.symLocTypeTag) THEN
            TypeTag (w, einfo. obj, TRUE, TRUE)
          ELSIF (einfo. attrib >= D.symLocLength0) THEN
            ArrayLength (w, einfo. obj, einfo. attrib, TRUE, TRUE)
          ELSE
            declFlags := {sideEffectParam, doNotMark, ignoreMark};
            IF einfo. passPerReference THEN
              INCL (declFlags, sideEffectReference)
            END;
            Declaration (w, einfo. obj, declFlags+{ignoreUsedDecl}, off)
          END;
          EnumerateSideEffects (NIL, einfo)
        END
      END;
      
      IF ~writeSep THEN  
        (* parameter list is empty, so we add a `void' to get a valid ANSI-C
           function prototype *)
        w. WriteString ("void")
      END;
      w. WriteChar (")")
    END FormalPars;
  
  PROCEDURE RightTypeExpr (t: D.Struct);
    VAR
      base: D.Struct;
      size: LONGINT;
    BEGIN
      IF (t # NIL) & ~CanUseTypeName (t, dmode) THEN
        CASE t. form OF
        | D.strPointer:
          Pointer (FALSE, t. base);
          RightTypeExpr (t. base)
        | D.strProc:
          IF ~(function IN dmode) THEN
            Pointer (FALSE, t)
          END;
          FormalPars (t)
        | D.strArray, D.strOpenArray:
          base := ArrayBase (t, size);
          IF (size >= 0) & ~(typeExpression IN dmode) THEN
            w. WriteChar ("[");
            w. WriteLInt (size, 0);
            w. WriteChar ("]")
          ELSE
            Pointer (FALSE, base)
          END;
          RightTypeExpr (base)
        ELSE  (* D.strNone, D.strPtr, D.strRecord: no right hand side *)
        END
      END
    END RightTypeExpr;
  
  PROCEDURE WriteCallConv (str: D.Struct);
    BEGIN
      IF (D.structExportsBEInfo IN str. flags) &
         (StdPragmas.targetOS. value^ = "Win32") THEN
        IF (str. beInfo(SystemFlags.Info). callConv = SystemFlags.callConvC) THEN
          w. WriteString (" __cdecl")
        ELSE
          w. WriteString (" __stdcall")
        END
      ELSE  (* standard calling convention *)
      END
    END WriteCallConv;
  
  BEGIN
    IF ((obj. moduleId = currModule) OR (ignoreOtherModule IN dmode)) & 
       (({StdTypes.objEmitted, StdTypes.objInProgress} * obj. beFlags = {}) OR
        ~(StdTypes.objInProgress IN obj. beFlags) & (ignoreMark IN dmode)) THEN
      (* mark the declaration as being in progress *)
      INCL (obj. beFlags, StdTypes.objInProgress);
      IF (obj. mode = D.objType) THEN
        INCL (obj. type. beFlags, StdTypes.structInProgress)
      END;
      IF ~(ignoreUsedDecl IN dmode) THEN
        (* generate declarations for all identifiers used to formulate the
           current declaration *)
        EmitUsedDeclarations (obj. type);
        IF (obj. mode = D.objTBProc) THEN
          TypeDeclaration (w, obj. data(D.Object). type, {}, off);
          EmitUsedDeclarations (obj. data(D.Object). type)
        END
      END;
      
      IF (obj. mode = D.objConst) THEN
        (* constants are introduced as preprocessor defines; only exported 
           constants are defined explicitly as part of the header file to allow
           easier interfacing from native C code; these defines are never used
           in the generated code itself *)
        NewLine (w, off);
        w. WriteString ("#define");
        DeclarationName (obj, dmode);
        w. WriteChar (" ");
        GenConst.Const (w, obj. data(D.Const), NIL)
        
      ELSE  (* write a true C declaration resp. definition *)
      
        IF (obj. mode = D.objTBProc) & (prototype IN dmode) THEN
          (* for type bound procedure: write additional defines into the
             header file containing the procedure's formal parameter list
             and its index in the method table *)
          NewLine (w, off);
          w. WriteString ("typedef ");
          LeftTypeExpr (obj. type, dmode);
          IF (obj. type. form = D.strProc) & ~(typeExpression IN dmode) THEN
            WriteCallConv (obj. type)
          END;
          w. WriteString ("(* _TBP_");
          DeclarationName (obj, {noSpace});
          w. WriteString (")");
          RightTypeExpr (obj. type);
          w. WriteString (";");
          NewLine (w, off);
          w. WriteString ("#define _TBN_");
          DeclarationName (obj, {noSpace});
          w. WriteString (" ");
          w. WriteLInt (obj. offset, 0)
        END;
        
        (* write declaration modifier *)
        IF (dmode*{formalParam, sideEffectParam, typeExpression} = {}) THEN
          NewLine (w, off)
        END;
        IF ~(typeExpression IN dmode) & (obj. mode = D.objType) THEN
          w. WriteString ("typedef ")
        ELSIF (obj. level = Sym.globalLevel) & (obj. mode # D.objField) THEN
          (* variables local to a procedure have the implicit storage class
             automatic; fields don't have a storage class at all; type-bound
             procedures are always external *)
          IF (external IN dmode) THEN
            w. WriteString ("extern ")
          ELSIF (static IN dmode) THEN
            w. WriteString ("static ")
          END
        END;
        IF (D.objVolatile IN obj. flags) THEN
          w. WriteString ("volatile ")
        END;
        IF (formalParam IN dmode) & (obj. mode = D.objVar) &
           StdTypes.PassPerReference (obj, TRUE) THEN
          w. WriteString ("const ")
        END;
        
        IF (obj. mode = D.objTBProc) & (typeExpression IN dmode) THEN
          w. WriteString ("_TBP_");
          DeclarationName (obj, {noSpace})
        ELSE
          (* write type expression, put the name inside it *)
          LeftTypeExpr (obj. type, dmode);
          IF (obj. type. form = D.strProc) & ~(typeExpression IN dmode) THEN
            WriteCallConv (obj. type)
          END;
          DeclarationName (obj, dmode);
          RightTypeExpr (obj. type);

          IF (dmode*{formalParam, sideEffectParam, function, typeExpression,
                     noSemicolon} = {}) OR (prototype IN dmode) THEN
            w. WriteChar (";")
          END
        END
      END;
      
      (* clear the `in progress' flags and signal that the declaration is
         finished by setting `emitted', unless we only wrote a declaration, and
         not the proper definition *)
      noDefinition := (external IN dmode) & (obj. mode = D.objVar);
      obj. beFlags := obj. beFlags / {StdTypes.objEmitted, StdTypes.objInProgress};
      IF (obj. mode = D.objType) & (obj. type. obj = obj) THEN
        obj. type. beFlags := obj. type. beFlags / 
                           {StdTypes.structEmitted, StdTypes.structInProgress};
        IF noDefinition OR (doNotMark IN dmode) THEN
          EXCL (obj. type. beFlags, StdTypes.structEmitted)
        END
      END;
      IF noDefinition OR (doNotMark IN dmode) THEN
        EXCL (obj. beFlags, StdTypes.objEmitted)
      END
    END
  END Declaration;

PROCEDURE TypeDeclaration* (w: TextRider.Writer; t: D.Struct; 
                            dmode: SET; off: INTEGER);
  BEGIN
    IF (t. obj = NIL) THEN
      (* if the type is an unnamed array, then get the innermost element type
         and write a declaration for it; otherwise declare the whole array *)
      WHILE Sym.TypeInGroup (t, D.grpArray) DO
        t := t. base
      END
    END;
    IF (t. obj # NIL) & (t. obj. moduleId # currModule) &
       ~(typeExpression IN dmode) THEN
      (* if type `t' is imported from another module, include its header 
         file (unless this already happened) *)
      GenInclude.Include (w, Sym.Module (t. obj), ".h", FALSE)
    ELSIF ((t. obj = NIL) OR (t. obj. moduleId = currModule)) &
       ({StdTypes.structEmitted, StdTypes.structInProgress}*t. beFlags = {}) &
       (t. form > D.strNone) OR
       (typeExpression IN dmode) THEN
      IF (t. obj # NIL) THEN
        Declaration (w, t. obj, dmode, off)
      ELSIF (typeExpression IN dmode) OR
            (t. beInfo(SystemFlags.Info). name # dummyName) THEN
        typeObject. moduleId := currModule;
        typeObject. mode := D.objType;
        typeObject. type := t;
        typeObject. name := t. beInfo(SystemFlags.Info). name;
        typeObject. beInfo := t. beInfo;
        typeObject. flags := {};
        typeObject. beFlags := {};
        t. obj := typeObject;
        Declaration (w, typeObject, dmode, off);
        t. obj := NIL
      END
    END
  END TypeDeclaration;

PROCEDURE VarDeclaration* (w: TextRider.Writer; name: ARRAY OF CHAR; 
                           t: D.Struct; dmode: SET; off: INTEGER);
  BEGIN
    typeObject. moduleId := currModule;
    typeObject. mode := D.objVar;
    typeObject. type := t;
    typeObject. name := dummyName;
    beInfo. name := dummyName;
    typeObject. beInfo := beInfo;
    typeObject. flags := {};
    typeObject. beFlags := {};
    COPY (name, dummyName^);
    Declaration (w, typeObject, dmode, off);
    COPY ("_dummy_", dummyName^)
  END VarDeclaration;


PROCEDURE Strings* (w: TextRider.Writer; list: GenConst.StringList);
  VAR
    baseType: ARRAY 64 OF CHAR;
    s: GenConst.StringList;
  BEGIN
    s := list;
    WHILE (s # NIL) DO
      NewLine (w, 0);
      w. WriteString ("static const ");
      IF (s. value. type. form = D.strStringConst8) THEN
        StdTypes.BasicTypes (D.strChar8, baseType)
      ELSE
        StdTypes.BasicTypes (D.strChar16, baseType)
      END;
      w. WriteString (baseType);
      w. WriteString (" ");
      w. WriteString (s. name);
      w. WriteString ("[] = ");
      GenConst.Const (w, s. value, NIL);
      w. WriteChar (";");
      s := s. next
    END
  END Strings;


PROCEDURE BuildObjList* (block: D.Object);
(* Returns values in `objList' and `objCount'.  *)

  PROCEDURE BuildList (obj: D.Object);
  (* Build a list from the binary tree in `obj' and append it to `objList'.  *)
    VAR
      new: ObjectList;
      i: LONGINT;
    BEGIN
      IF (obj # NIL) THEN
        BuildList (obj. leftObj);
        
        IF (LEN (objList^) = objCount) THEN  (* overflow, extend list *)
          NEW (new, LEN (objList^)*2);
          FOR i := 0 TO objCount-1 DO
            new[i] := objList[i]
          END;
          objList := new
        END;
        objList[objCount] := obj;
        INC (objCount);
        
        BuildList (obj. rightObj)
      END
    END BuildList;
  
  PROCEDURE QuickSort (l, r: LONGINT);
  (* Sort `objList' by object position, smaller values first.  *)
    VAR
      i, j, min, v: LONGINT;
    
    PROCEDURE Swap (i, j: LONGINT);
      VAR
        x: D.Object;
      BEGIN
        x := objList[i];
        objList[i] := objList[j];
        objList[j] := x
      END Swap;
    
    BEGIN
      IF (l+8 > r) THEN  (* selection sort *)
        FOR i := l TO r DO
          min := i;
          FOR j := i+1 TO r DO
            IF (objList[j]. pos < objList[min]. pos) THEN
              min := j
            END
          END;
          Swap (i, min)
        END
      ELSE  (* quick sort *)
        i := l-1; j := r; 
        Swap ((l+r) DIV 2, r);
        v := objList[r]. pos;
        LOOP
          REPEAT 
            INC (i)
          UNTIL (i = r) OR (objList[i]. pos >= v);
          REPEAT
            DEC (j)
          UNTIL (j = l) OR (objList[j]. pos <= v);
          IF (i >= j) THEN
            EXIT
          END;
          Swap (i, j)
        END;
        Swap (i, r);
        QuickSort (l, j); QuickSort (i+1, r)
      END
    END QuickSort;
  
  BEGIN  
    objCount := 0;
    BuildList (block. localDecl);
    QuickSort (0, objCount-1)
  END BuildObjList;

PROCEDURE TypeDescrName* (w: TextRider.Writer; t: D.Struct; 
                          variable: BOOLEAN);
(* Writes the the name of the type descriptor type (variable=FALSE) resp. the
   type descriptor variable (variable=TRUE) associated with `t'.  If `t' is a
   pointer type then the pointer base type is used (which must be a record). *)
  BEGIN
    IF (t. form = D.strPointer) THEN
      t := t. base
    END;
    IF variable THEN
      w. WriteString (t. beInfo(SystemFlags.Info). name^);
      w. WriteString ("_td")
    ELSE
      w. WriteString ("_TypeDesc")
    END
  END TypeDescrName;

PROCEDURE WriteScalarType* (w: TextRider.Writer;
                            type: D.Struct; unsigned, pointer: BOOLEAN);
  VAR
    str: ARRAY 64 OF CHAR;
    pos: INTEGER;
    flags: SET;
    found: BOOLEAN;
  BEGIN
    IF (type. form = D.strProc) THEN
      flags := {typeExpression, ignoreUsedDecl, doNotMark, ignoreMark,
                ignoreOtherModule};
      IF pointer THEN
        INCL (flags, functionPointer)
      END;
      TypeDeclaration (w, type, flags, 0)
    ELSIF Sym.TypeInGroup (type, D.grpPtr) THEN
      w. WriteString ("void*");
      IF pointer THEN
        w. WriteChar ("*")
      END
    ELSE
      StdTypes.BasicTypes (type. form, str);
      IF unsigned THEN
        w. WriteString ("unsigned ");
        Str.FindNext ("signed ", str, 0, found, pos);
        IF found & (pos = 0) THEN
          Str.Delete (str, 0, 7)
        ELSE
          Str.FindNext ("unsigned ", str, 0, found, pos);
          IF found & (pos = 0) THEN
            Str.Delete (str, 0, 9)
          END
        END
      END;
      w. WriteString (str);
      IF pointer THEN
        w. WriteChar ("*")
      END
    END
  END WriteScalarType;

PROCEDURE WriteScalarCast* (w: TextRider.Writer; type: D.Struct; 
                            unsigned, pointer, const: BOOLEAN);
  BEGIN
    w. WriteChar ("(");
    IF const THEN
      w. WriteString ("const ")
    END;
    WriteScalarType (w, type, unsigned, pointer);
    w. WriteChar (")")
  END WriteScalarCast;


PROCEDURE RegisterTBCall* (proc: D.Object);
(* If the index of `proc' isn't know yet, store a pointer to the procedure so
   we can patch in the correct value later.  *)
  CONST
    init = 8;
    incr = 8;
  VAR
    len, i, oldLen: LONGINT;
    tbNew: ObjectList;
  BEGIN
    IF (proc. mode = D.objTBProc) & (proc. offset < 0) THEN
      IF (tbCallList = NIL) OR (ABS(proc. offset)-1 >= LEN (tbCallList^)) THEN
        IF (tbCallList = NIL) THEN
         len := init
        ELSE
          len := LEN (tbCallList^)
        END;
        WHILE (ABS(proc. offset)-1 >= len) DO
          INC (len, incr)
        END;
        NEW (tbNew, len);
        IF (tbCallList # NIL) THEN
          oldLen := LEN (tbCallList^);
          FOR i := 0 TO oldLen-1 DO
            tbNew[i] := tbCallList[i]
          END
        ELSE
          oldLen := 0
        END;
        FOR i := oldLen TO len-1 DO
          tbNew[i] := NIL
        END;
        tbCallList := tbNew
      END;
      
      tbCallList[ABS(proc. offset)-1] := proc
    END
  END RegisterTBCall;

PROCEDURE PatchTBCalls* (w: TextRider.Writer);
  VAR
    i: LONGINT;
  BEGIN
    IF (tbCallList # NIL) THEN
      FOR i := 0 TO LEN (tbCallList^)-1 DO
        IF (tbCallList[i] # NIL) THEN
          w. WriteLn;
          w. WriteString ("#define _TB");
          w. WriteLInt (i+1, 0);
          w. WriteString (" ");
          w. WriteLInt (tbCallList[i]. offset, 0)
        END
      END
    END
  END PatchTBCalls;


PROCEDURE Name (w: TextRider.Writer; name: ARRAY OF CHAR): INTEGER;
(* Writes a variable declaration containing `name' that mimicks the layout of
   open arrays on the heap, i.e. it's length is stored before the array value.
   If X is the result of the call, then the address of name part of the
   variable is `&_nX.name'.  *)
  VAR
    id, len: INTEGER;
  BEGIN
    id := nameCounter;
    len := Str.Length (name)+1;
    INC (nameCounter);
    
    NewLine (w, 0);
    w. WriteString ("static const struct {");
    NewLine (w, 1);
    WriteScalarType (w, D.struct[D.strLongInt], FALSE, FALSE);
    w. WriteString (" length;");
    NewLine (w, 1);
    w. WriteString ("void* pad;");
    NewLine (w, 1);
    w. WriteString ("const char name[");
    w. WriteInt (len, 0);
    w. WriteString ("];");
    NewLine (w, 0);
    w. WriteString ("} _n");
    w. WriteInt (id, 0);
    w. WriteString (" = {");
    w. WriteInt (len, 0);
    w. WriteString (', NULL, {"');
    w. WriteString (name);
    w. WriteString ('"}};');
    RETURN id
  END Name;

PROCEDURE PtrList (w: TextRider.Writer; root: D.Object; mode: SHORTINT): INTEGER;
(* Writes a list of exported `mode' objects.  *)
  VAR
    id, len: INTEGER;
  
  PROCEDURE CountObjects (node: D.Object): INTEGER;
    VAR
      c: INTEGER;
    BEGIN
      IF (node # NIL) THEN
        IF (node. mode = mode) & (D.objIsExported IN node. flags) THEN
          c := 1
        ELSE
          c := 0
        END;
        RETURN CountObjects (node. leftObj)+CountObjects (node. rightObj)+c
      ELSE
        RETURN 0
      END
    END CountObjects;
  
  PROCEDURE WriteObjects (node: D.Object);
    BEGIN
      IF (node # NIL) THEN
        WriteObjects (node. leftObj);
        IF (node. mode = mode) & (D.objIsExported IN node. flags) THEN
          NewLine (w, 1);
          WriteScalarCast (w, D.struct[D.strPtr], FALSE, FALSE, TRUE);
          w. WriteString ("&");
          w. WriteString (node. beInfo(SystemFlags.Info). name^);
          w. WriteString (",");
        END;
        WriteObjects (node. rightObj)
      END
    END WriteObjects;
  
  BEGIN
    id := ptrListCounter;
    len := CountObjects (root);
    INC (ptrListCounter);
    
    NewLine (w, 0);
    w. WriteString ("static const struct {");
    NewLine (w, 1);
    WriteScalarType (w, D.struct[D.strLongInt], FALSE, FALSE);
    w. WriteString (" length;");
    NewLine (w, 1);
    w. WriteString ("void* pad;");
    NewLine (w, 1);
    w. WriteString ("const ");
    WriteScalarType (w, D.struct[D.strPtr], FALSE, FALSE);
    w. WriteString (" list[");
    w. WriteInt (len, 0);
    w. WriteString ("];");
    NewLine (w, 0);
    w. WriteString ("} _p");
    w. WriteInt (id, 0);
    w. WriteString (" = {");
    w. WriteInt (len, 0);
    w. WriteString (', NULL, {');
    WriteObjects (root);
    NewLine (w, 0);
    w. WriteString ('}};');
    RETURN id
  END PtrList;

PROCEDURE ModuleDescriptor* (w: TextRider.Writer; mod: D.Object);
  VAR
    id, pid, vid: INTEGER;
  BEGIN
    (* emit lists of exported procedures and variables *)
    pid := PtrList (w, mod. localDecl, D.objProc);
    vid := PtrList (w, mod. localDecl, D.objVar);
    
    (* declare the module name *)
    id := Name (w, mod. name^);
    
    NewLine (w, 0);
    w. WriteString ("static struct _MD ");
    w. WriteString (mod. beInfo(SystemFlags.Info). name^);
    w. WriteString ("_md = {");
    NewLine (w, 1);
    w. WriteString ("NULL, ");
    NewLine (w, 1);
    w. WriteString ("&Kernel__ModuleDesc_td.td, ");
    NewLine (w, 1);
    w. WriteChar ("{");
    
    (* next descriptor *)
    NewLine (w, 2);
    w. WriteString ("NULL, ");
    (* module name *)
    NewLine (w, 2);
    WriteScalarCast (w, D.struct[D.strChar8], FALSE, TRUE, TRUE);
    w. WriteString ("_n"); 
    w. WriteInt (id, 0);
    w. WriteString (".name, ");
    (* module key *)
    NewLine (w, 2);
    w. WriteString ("-1, ");
    (* type descriptor list *)
    NewLine (w, 2);
    w. WriteString ("NULL,");
    (* list of procedure pointers *)
    NewLine (w, 2);
    w. WriteString ("_p");
    w. WriteInt (pid, 0);
    w. WriteString (".list,");
    (* list of variable pointers *)
    NewLine (w, 2);
    w. WriteString ("_p");
    w. WriteInt (vid, 0);
    w. WriteString (".list,");
    (* fingerprint *)
    NewLine (w, 2);
    GenConst.Int (w, mod. data(D.Const). int);
    
    NewLine (w, 1);
    w. WriteChar ("}");
    NewLine (w, 0);
    w. WriteString ("};")
  END ModuleDescriptor;

PROCEDURE TBProcArray (w: TextRider.Writer; t: D.Struct): INTEGER;
  VAR
    id, i: INTEGER;
    len: LONGINT;
  
  PROCEDURE WriteTBProc (record: D.Struct; index: INTEGER);
    VAR
      obj: D.Object;
    BEGIN
      IF (D.structNoDescriptor IN record. flags) THEN
        (* if the record has no type descriptor, then we don't know anything
           about its type-bound procedures; they might not even exist as
           linkage symbols *)
        w. WriteString ("NULL")
      ELSE
        obj := record. decl;
        WHILE (obj # NIL) &
              ((obj. mode = D.objField) OR (obj. offset # index)) DO
          obj := obj. rightObj
        END;
        IF (obj = NIL) THEN
          WriteTBProc (record. base, index)
        ELSE
          w. WriteString (obj. beInfo(SystemFlags.Info). name^)
        END
      END
    END WriteTBProc;
  
  BEGIN
    id := recordCounter;
    INC (recordCounter);
    len := Sym.NumberOfTBProcs (t, TRUE);
    
    NewLine (w, 0);
    w. WriteString ("static const struct {");
    NewLine (w, 1);
    WriteScalarType (w, D.struct[D.strLongInt], FALSE, FALSE);
    w. WriteString (" length;");
    NewLine (w, 1);
    w. WriteString ("void* pad;");
    NewLine (w, 1);
    w. WriteString ("const void* tbprocs[");
    IF (len = 0) THEN  (* ANSI-C forbids arrays of length zero *)
      w. WriteInt (1, 0)
    ELSE
      w. WriteLInt (len, 0)
    END;
    w. WriteString ("];");
    NewLine (w, 0);
    w. WriteString ("} _tb");
    w. WriteInt (id, 0);
    w. WriteString (" = {");
    w. WriteLInt (len, 0);
    w. WriteString (", NULL, {");
    
    IF (len = 0) THEN
      NewLine (w, 1);
      w. WriteString ("NULL")
    ELSE
      FOR i := 0 TO SHORT (len)-1 DO
        NewLine (w, 1);
        w. WriteString ("(void*)");
        WriteTBProc (t, i);
        IF (i # len-1) THEN
          w. WriteString (", ")
        END
      END
    END;
    
    NewLine (w, 0);
    w. WriteString ("}};");
    RETURN id
  END TBProcArray;

PROCEDURE TypeDescriptor* (w: TextRider.Writer; mod: D.Object;
                           t, link: D.Struct; extern: BOOLEAN);
  VAR
    id, tbId: INTEGER;

  PROCEDURE BaseTypes (w: TextRider.Writer; t: D.Struct);
  (* Writes a variable declaration containing the array of base types of `t'
     that mimicks the layout of open arrays on the heap, i.e. it's length is 
     stored before the array value.  *)
    
    PROCEDURE WriteType (t: D.Struct; last: BOOLEAN);
      BEGIN
        IF (t # NIL) THEN
          WriteType (t. base, FALSE);
          NewLine (w, 2);
          IF (D.structNoDescriptor IN t. flags) THEN 
            w. WriteString ("NULL")
          ELSE
            w. WriteChar ("&");
            TypeDescrName (w, t, TRUE);
            w. WriteString (".td")
          END;
          IF ~last THEN
            w. WriteString (", ")
          END
        END
      END WriteType;
    
    BEGIN
      NewLine (w, 0);
      w. WriteString ("static const struct {");
      NewLine (w, 1);
      WriteScalarType (w, D.struct[D.strLongInt], FALSE, FALSE);
      w. WriteString (" length;");
      NewLine (w, 1);
      w. WriteString ("void* pad;");
      NewLine (w, 1);
      w. WriteString ("_Type btypes[");
      w. WriteLInt (t. len+1, 0);
      w. WriteString ("];");
      NewLine (w, 0);
      w. WriteString ("} ");
      TypeDescrName (w, t, TRUE);
      w. WriteString ("b = {");
      NewLine (w, 1);
      w. WriteLInt (t. len+1, 0);
      w. WriteString (', ');
      NewLine (w, 1);
      w. WriteString ("NULL, ");
      NewLine (w, 1);
      w. WriteChar ("{");
      WriteType (t, TRUE);
      NewLine (w, 1);
      w. WriteChar ("}");
      NewLine (w, 0);
      w. WriteString ("};")
    END BaseTypes;

  BEGIN
    NewLine (w, 0);
    IF extern THEN
      w. WriteString ("extern ");
      w. WriteString ("struct _TD ");
      TypeDescrName (w, t, TRUE);
      w. WriteChar (";")
      
    ELSE
      (* declare the type name, unless `t' is an unnamed type or it is declared
         inside a procedure *)
      IF (t. obj = NIL) OR (t. obj. level > Sym.globalLevel) THEN
        id := -1
      ELSE
        id := Name (w, t. obj. name^)
      END;
      
      (* build "open" array with references to types *)
      BaseTypes (w, t);
      
      (* build "open" array with references to type-bound procedures *)
      tbId := TBProcArray (w, t);
      NewLine (w, 0);

      w. WriteString ("struct _TD ");
      TypeDescrName (w, t, TRUE);
      w. WriteString (" = {");
      NewLine (w, 1);
      w. WriteString ("NULL,");
      NewLine (w, 1);
      w. WriteString ("&Types__TypeDesc_td.td,");
      NewLine (w, 1);
      w. WriteChar ("{");

      (* base types *)
      NewLine (w, 2);
      TypeDescrName (w, t, TRUE);
      w. WriteString ("b.btypes,");
      (* type-bound procedures *)
      NewLine (w, 2);
      w. WriteString ("_tb");
      w. WriteInt (tbId, 0);
      w. WriteString (".tbprocs,");
      (* type name *)
      NewLine (w, 2);
      IF (id >= 0) THEN
        WriteScalarCast (w, D.struct[D.strChar8], FALSE, TRUE, TRUE);
        w. WriteString ("_n"); 
        w. WriteInt (id, 0);
        w. WriteString (".name,")
      ELSE
        w. WriteString ("NULL,")
      END;
      (* module reference *)
      NewLine (w, 2);
      w. WriteChar ("&");
      w. WriteString (mod. beInfo(SystemFlags.Info). name^);
      w. WriteString ("_md.md,");
      (* extension level *)
      NewLine (w, 2);
      w. WriteLInt (t. len, 0);
      w. WriteString (", ");
      (* padding *)
      NewLine (w, 2);
      w. WriteString ("'0', '1',");
      (* type size *)
      NewLine (w, 2);
      w. WriteString ("sizeof(");
      w. WriteString (t. beInfo(SystemFlags.Info). name^);
      w. WriteString ("),");
      (* next descriptor *)
      NewLine (w, 2);
      IF (link # NIL) THEN
        w. WriteChar ("&");
        TypeDescrName (w, link, TRUE);
        w. WriteString (".td")
      ELSE
        w. WriteString ("NULL")
      END;
      NewLine (w, 1);
      w. WriteChar ("}");
      NewLine (w, 0);
      w. WriteString ("};");

      INCL (t. beFlags, StdTypes.structTDEmitted)
    END
  END TypeDescriptor;



PROCEDURE InitReservedWords;
    
  PROCEDURE RW (id: ARRAY OF CHAR);
    VAR
      i: INTEGER;
      hash: LONGINT;
    BEGIN
      hash := 0; i := 0;
      WHILE (id[i] # 0X) DO
        INC (hash, LONG (ORD (id[i])));
        INC (i)
      END;
      hash := hash MOD 256;
      IF (rwList[hash] = "") THEN
        COPY (id, rwList[hash])
      ELSE
        ASSERT (rwList[hash+1] = "");
        COPY (id, rwList[hash+1])
      END
    END RW;
  
  BEGIN
    (* reserved words of ANSI-C *)
    RW ("auto"); RW ("break"); RW ("case"); RW ("char"); RW ("const"); 
    RW ("continue"); RW ("default"); RW ("do"); RW ("double"); RW ("else"); 
    RW ("enum"); RW ("extern"); RW ("float"); RW ("for"); RW ("goto"); 
    RW ("if"); RW ("int"); RW ("long"); RW ("register"); RW ("return"); 
    RW ("short"); RW ("signed"); RW ("sizeof"); RW ("static"); RW ("struct"); 
    RW ("switch"); RW ("typedef"); RW ("union"); RW ("unsigned"); RW ("void"); 
    RW ("volatile"); RW ("while"); RW ("fortran"); RW ("asm"); 
    (* C++ reserved words *)
    RW ("bool"); RW ("catch"); RW ("class"); RW ("delete"); RW ("false"); 
    RW ("friend"); RW ("inline"); RW ("new"); RW ("operator"); RW ("private"); 
    RW ("protected"); RW ("public"); RW ("template"); RW ("true"); RW ("try");
    RW ("this"); RW ("virtual"); RW ("throw");
    (* standard C functions used by the compiler; the name of every function
       prototype in __libc.h that doesn't have an underscore in it has to 
       appear here; strcmpl is provided by __oo2c.c *)
    RW ("malloc"); RW ("alloca"); RW ("memcpy"); RW ("memset"); RW ("strcmp");
    RW ("strcmpl"); RW ("NULL")
  END InitReservedWords;

BEGIN
  InitReservedWords;
  NEW (dummyName, 16);
  COPY ("_dummy_", dummyName^);
  NEW (typeObject);
  D.InitObject (typeObject, "", D.objType, D.undefPos);
  typeObject. level := -1;
  NEW (beInfo);
  NEW (objList, 500);
  objCount := 0;
  tbCallList := NIL
END GenDecl.
