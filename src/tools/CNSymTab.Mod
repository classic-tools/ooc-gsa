(*	$Id: CNSymTab.Mod,v 1.2 1999/06/04 16:11:48 acken Exp $	*)
MODULE CNSymTab;
(*  Scans declarations of a module and creates the symbol table.
    Copyright (C) 1998, 1999  Michael van Acken

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
  Out, Strings, S := CNScanner, AST := CNAST;

(* 

The data structure used to manage a module's symbol table is similar
to the one of OOC, but it is simplified in a number of points.

Object:
o the following fields do not exist: beFlags, data
o a type-bound procedure's receiver is stored in a field of its own

Struct:
o the following fields do not exist: flags, beFlags
o a new type id, `strName', has been introduced; it is the id of every
  using occurence of a type name, and it refers to the type
  declaration (which in turn refers to the actual type); this "new"
  type form is introduced to handle type aliasing without any loss of
  information 

*)


TYPE
  Usable* = POINTER TO UsableDesc;
  Struct* = POINTER TO StructDesc;
  Object* = POINTER TO ObjectDesc;

TYPE
  UsableDesc = RECORD
    (* common base type of type and object descriptors; the peculiar name is
       taken from the corresponding data type in OOC :-] *)
    (S.InfoDesc)
    localTo-: Usable;
    (* scope in which this object is declared; for fields and type-bound
       procedures this is the record (i.e., a `Struct') they belong to, for all
       other declarations it is the module or procedure they are declarared 
       in (i.e., this field refers to an `Object'); for a type this refers to
       the type constructor it is part of, or to the module/procedure if it is
       not nested in a type constructor *)
    useList-, useTail: AST.Ident;
    (* list of uses (use-chain) of the given entity; the following kinds of
       uses are distinguished:
        o use of `Struct':
           - `Object.type' for type, variable, field, and parameter 
             declarations
           - `Struct.base' for use as a pointer base type, as the result type
             of a procedure type, as the element type of an array, or as base
             type of a record
           - designator ... 
        o use of `Object':
           - designator ...
       Note that uses of a type _name_ are recorded in the use list of the
       corresponding `Struct', not that of the `Object'  *)
  END;

TYPE
  ObjectDesc = RECORD 
    (UsableDesc)
    mode-: SHORTINT;  
    (* identifies the kind of object, eg, constant, type, variable, etc.; for
       a complete list look at the `objXXX' constants below *)
    name-: S.String;  
    (* name of object *)
    type-: Struct;
    (* the object's type *)
    leftObj-, rightObj*: Object;  
    (* links to sons in scope tree, the root is stored in `Object.localDecl'
       (for modules and procedures);  record fields and type-bound procedures
       are stored in a list linked with `Object.rightObj' whose head is stored
       in `Struct.decl'; a list of symbol tables, e.g. the one passed to
       `CreateSymTab', also uses `rightObj' to point to the next list element
       *)
    localDecl-: Object;
    (* for a module or a procedure this is the root of a binary tree containing
       the declarations in its visibility scope; nodes of the the tree are 
       linked by the fields `leftObj' and `rightObj'; if the object stands in
       for an imported module, this pointer refers to the module's symbol 
       table *)
    flags-: SET;
    (* various flags, see `objXXX' constants below *)
    identDef-: AST.IdentDef;
    (* refers to the identifier of the object's declaration *)
    pos-: LONGINT;  
    (* file position of the object's declaration; use this value when referring
       to a declaration in an error or a warning *);
    info*: S.Info;
    (* place to stuff information for algorithms working on objects *)
  END;

TYPE
  Module* = POINTER TO ModuleDesc;
  ModuleDesc = RECORD
    (ObjectDesc)
    ast-: AST.Module;
    (* abstract syntax tree of the module, NIL for predefined modules *)
  END;

TYPE
  TBProc* = POINTER TO TBProcDesc;
  TBProcDesc = RECORD
    (ObjectDesc)
    receiver-: Object;
    (* receiver of type-bound procedure; an instance of `objVar' or 
       `objVarPar' *)
    super-: TBProc;
    (* next higher procedure of which this type-bound procedure is a 
       redefinition; NIL if the procedure is no redefinition *)
  END;
  
CONST  (* object modifiers and signals (values for `Object.flags') *)
  objIsExported* = 0;
  (* object is exported, i.e. visible outside the current module;  the flag
     `objIsExportedReadOnly' toggles between read-only and read/write export *)
  objIsExportedReadOnly* = 1;
  (* variable or field is not writable outside this module *)
  objIsForwardDecl* = 2;
  (* type or procedure was created as a result of a forward declaration and is
     not properly defined yet; this flags is cleared as soon as the header of 
     the actual procedure definition is parsed, or after the forward declared 
     type has been defined completely*)
  objWasForwardDecl* = 3;
  (* set if a the object has been a forward declaration, but was resolved in 
     the meantime; set at the same time as `objIsForwardDecl' is cleared *)
  objIsParameter* = 4;
  (* variable is part of a procedure's parameter list or its receiver *)

CONST
  (* these values identify the various declared objects (see `Object. mode');  
     note: variables are distinguished between variable parameters `objVarPar'
     and normal variables & value parameters `objVar' *)
  objUndef* = 0; objConst* = 1; objType* = 2;   objVar* = 3;  objVarPar* = 4; 
  objField* = 5; objProc* = 6;  objTBProc* = 7; objModule* = 8; 
  objRestParam* = 9;  (* special formal parameter `...' (for external C) *)

TYPE
  StructDesc = RECORD 
    (UsableDesc)
    form-: SHORTINT;
    (* class of type, see `strXXX' constants below *)
    base-: Struct;
    (* contains pointer base type, array element type, record base type (NIL
       if the record isn't an extension), or a procedure result type *)
    decl-: Object;
    (* the formal parameter list for procedure types and for procedure 
       declarations, or, for record types, the list of fields and type-bound
       procedures; the parameters (fields, type-bound procedures) are linked 
       with `Object.rightObj'; for `strName' types, this refers to the used
       type declaration *)
    obj-: Object;
    (* this field is NIL for type constructs that are not associated with a
       name, otherwise it's the name (the object) that is assigned to
       this type *)
    pos-: LONGINT;
    (* file position of the type constructor that defined this type; note: this
       is not equal to the position of a type declaration that provides a name
       for the type *)
    extList-, nextExt-: Struct;
    (* list of extensions of the record type *)
  END;

CONST
  (* The following values define different types.  The first group (strUndef to
     strNone) defines atomic types, the second structured types.  The symbols
     `strNil' and `strStringConst' denote the special types of NIL and string
     constants, `strNone' the result type of a proper procedure.  To have alias
     information available in the symbol table, a new structure `strName' is
     introduced.  Such a struct is a place holder for the object of the 
     referred type.  *)
  strName* = 0;     strBoolean* = 1;  strChar* = 2;       strLongChar* = 3;
  strShortInt* = 4; strInteger* = 5;  strLongInt* = 6;    strHugeInt* = 7;
  strReal* = 8;     strLongReal* = 9; strComplex* = 10;   strLongComplex* = 11;
  strSet8* = 12;    strSet16* = 13;   strSet32* = 14;     strSet64* = 15;
  strByte* = 16;    strPtr* = 17;     strStringConst*=18; strNil* = 19;
  strNone* = 20;    strUndef* = 21;
  (* in the compiler sources addresses are assigned the virtual type 
     `strAddress'; this type is always an alias to an existing integer type;
     on 32bit systems it is equivalent to LONGINT *)
  strAddress* = strLongInt;
  (* markers for structured types;  arrays are separated into `normal', i.e.
     fixed length arrays, and open arrays *)
  strPointer* = 32; strProc* = 33; strArray* = 34; strOpenArray* = 35; 
  strRecord* = 36;


VAR
  currModule: AST.Module;

VAR
  struct: ARRAY strUndef+1 OF Struct;
  (* structures of predefined types, set by `InitPredef' *)
  predef-: Module;
  (* this visibility scope declares the predefined constants, types, functions,
     and procedures; it is lowest possible scope *)
  system-: Module;
  (* the predefined module SYSTEM *)



PROCEDURE Err (pos: LONGINT; msg: ARRAY OF CHAR);
  BEGIN
    Out.String ("In file ");
    Out.String (currModule. startSymbol. file^);
    Out.String (": ");
    Out.Ln;
    Out.LongInt (pos, 0);
    Out.String (": ");
    Out.String (msg);
    Out.Ln;
    HALT (1)
  END Err;

PROCEDURE MultDeclErr (pos: LONGINT);
  BEGIN
    Err (pos, "Multiple declaration of same name")
  END MultDeclErr;


PROCEDURE (usable: Usable) AddUse* (use: AST.Ident);
  BEGIN
    use. obj := usable;
    use. nextUse := NIL;
    IF (usable. useList = NIL) THEN
      usable. useList := use;
      usable. useTail := use
    ELSE
      usable. useTail. nextUse := use;
      usable. useTail := use
    END
  END AddUse;

PROCEDURE (usable: Usable) RemoveUse* (use: AST.Ident);
  VAR
    ptr: AST.Ident;
  BEGIN
    IF (usable. useList = use) THEN
      usable. useList := usable. useList. nextUse;
      IF (usable. useList = NIL) THEN
        usable. useTail := NIL
      END
    ELSE
      ptr := usable. useList;
      WHILE (ptr. nextUse # use) DO
        ptr := ptr. nextUse
      END;
      IF (use. nextUse = NIL) THEN
        ptr. nextUse := NIL;
        usable. useTail := ptr
      ELSE
        ptr. nextUse := use. nextUse
      END
    END;
    use. obj := NIL;
    use. nextUse := NIL
  END RemoveUse;

PROCEDURE (record: Struct) AddExt (ext: Struct);
  VAR
    ptr: Struct;
  BEGIN
    ASSERT (record. form = strRecord);
    ext. nextExt := NIL;
    IF (record. extList = NIL) THEN
      record. extList := ext
    ELSE
      ptr := record. extList;
      WHILE (ptr. nextExt # NIL) DO
        ptr := ptr. nextExt
      END;
      ptr. nextExt := ext
    END
  END AddExt;

PROCEDURE (record: Struct) RemoveExt (ext: Struct);
  VAR
    ptr: Struct;
  BEGIN
    IF (record. extList = ext) THEN
      record. extList := ext. nextExt
    ELSE
      ptr := record. extList;
      WHILE (ptr. nextExt # ext) DO
        ptr := ptr. nextExt
      END;
      ptr. nextExt := ext. nextExt
    END;
    ext. nextExt := NIL
  END RemoveExt;


PROCEDURE (obj: Object) SetType (type: Struct);
  BEGIN
    obj. type := type
  END SetType;

PROCEDURE (struct: Struct) SetBase (base: Struct);
  BEGIN
    struct. base := base
  END SetBase;


PROCEDURE NewObject (mode: SHORTINT; name: S.String; type: Struct;
                     pos: LONGINT): Object;
  VAR
    obj: Object;
    mod: Module;
    tbProc: TBProc;
  BEGIN
    IF (mode = objModule) THEN
      NEW (mod);
      mod. ast := NIL;
      obj := mod;
    ELSIF (mode = objTBProc) THEN
      NEW (tbProc);
      tbProc. receiver := NIL;
      tbProc. super := NIL;
      obj := tbProc
    ELSE
      NEW (obj)
    END;
    obj. localTo := NIL;
    obj. useList := NIL;
    obj. useTail := NIL;
    obj. mode := mode;
    obj. name := name;
    obj. type := NIL;
    obj. leftObj := NIL;
    obj. rightObj := NIL;
    obj. localDecl := NIL;
    obj. flags := {};
    obj. identDef := NIL;
    obj. pos := pos;
    obj. SetType (type);
    obj. info := NIL;
    RETURN obj
  END NewObject;

PROCEDURE NewStruct (form: SHORTINT; pos: LONGINT): Struct;
  VAR
    struct: Struct;
  BEGIN
    NEW (struct);
    struct. localTo := NIL;
    struct. useList := NIL;
    struct. useTail := NIL;
    struct. form := form;
    struct. pos := pos;
    struct. base := NIL;
    struct. decl := NIL;
    struct. obj := NIL;
    struct. extList := NIL;
    struct. nextExt := NIL;
    RETURN struct
  END NewStruct;

PROCEDURE NewModule (modName: ARRAY OF CHAR; ast: AST.Module; 
                     pos: LONGINT): Module;
(* Allocate memory for module, and initialize it.  *)
  VAR
    obj: Object;
    mod: Module;
    str: S.String;
  BEGIN
    NEW (str, Strings.Length (modName)+1);
    COPY (modName, str^);
    obj := NewObject (objModule, str, NIL, pos);
    mod := obj(Module);
    mod. localTo := predef;
    mod. ast := ast;
    RETURN mod
  END NewModule;


PROCEDURE InsertDecl (scope: Usable; obj: Object): Object;
(* Inserts `obj' into `scope'.  If no declaration `obj. name^' exists, result 
   is NIL.  Otherwise nothing is inserted and the previous declaration of that
   name is returned. 
   pre: `scope IS Object' with `scope. mode IN {objModule, objProc, 
     objTBProc}, or `scope IS Struct' with `scope. form = strRecord' *)
    
  PROCEDURE InsertInTree (VAR tree: Object): Object;
    VAR
      ptr: Object;
    BEGIN
      IF (tree = NIL) THEN
        tree := obj;
        RETURN NIL
      ELSE
        ptr := tree;
        LOOP
          IF (obj. name^ < ptr. name^) THEN
            IF (ptr. leftObj = NIL) THEN
              ptr. leftObj := obj;
              RETURN NIL
            ELSE
              ptr := ptr. leftObj
            END
          ELSIF (ptr. name^ < obj. name^) THEN
            IF (ptr. rightObj = NIL) THEN
              ptr. rightObj := obj;
              RETURN NIL
            ELSE
              ptr := ptr. rightObj
            END
          ELSE  
            (* (ptr. name^ = obj. name^), previous decl of same name exists *)
            RETURN ptr
          END
        END
      END
    END InsertInTree;

  PROCEDURE InsertInList (VAR list: Object): Object;
    VAR
      ptr: Object;
    BEGIN
      IF (list = NIL) THEN
        list := obj;
        RETURN NIL
      ELSE
        ptr := list;
        LOOP
          IF (ptr. name^ = obj. name^) THEN
            RETURN ptr
          ELSIF (ptr. rightObj = NIL) THEN
            ptr. rightObj := obj;
            RETURN NIL
          ELSE
            ptr := ptr. rightObj
          END
        END
      END
    END InsertInList;

  BEGIN
    obj. leftObj := NIL; 
    obj. rightObj := NIL; 
    obj. localTo := scope;
    WITH scope: Object DO
      RETURN InsertInTree (scope. localDecl)
    | scope: Struct DO
      RETURN InsertInList (scope. decl)
    END
  END InsertDecl;

PROCEDURE InsertUnique (scope: Usable; obj: Object);
  VAR
    o: Object;
  BEGIN
    o := InsertDecl (scope, obj);
    IF (o # NIL) THEN
      MultDeclErr (obj. pos)
    END
  END InsertUnique;

PROCEDURE ScopeObject* (obj: Object): BOOLEAN;
  BEGIN
    RETURN (obj. mode =  objModule) OR
           (obj. mode =  objProc) OR
           (obj. mode =  objTBProc)
  END ScopeObject;

PROCEDURE Redefinition* (base, proc: TBProc): BOOLEAN;
  BEGIN
    REPEAT
      proc := proc. super
    UNTIL (proc = base) OR (proc = NIL);
    RETURN (proc = base)
  END Redefinition;

PROCEDURE ResolveType* (type: Struct): Struct;
  BEGIN
    WHILE (type. form = strName) DO
      type := type. decl. type
    END;
    RETURN type
  END ResolveType;

PROCEDURE FindDecl* (scope: Usable; VAR name: ARRAY OF CHAR): Object;
(* Finds the declaration `name' in the visibility scope `scope'.  If no such
   declaration exists, NIL is returned.  Note: The returned object may not
   be visible in the current module.
   pre: `scope IS Object' with `scope. mode IN {objModule, objProc, 
     objTBProc}, or `scope IS Struct' with `scope. form = strRecord' *)
  VAR
    obj: Object;
    base: Struct;
  BEGIN
    IF (scope = NIL) THEN
      RETURN NIL
    ELSE
      WITH scope: Object DO
        obj := scope. localDecl;
        WHILE (obj # NIL) & (obj. name^ # name) DO
          IF (name < obj. name^) THEN
            obj := obj. leftObj
          ELSE
            obj := obj. rightObj
          END
        END;
        
        IF (obj = NIL) & (scope. type # NIL) THEN
          ASSERT (scope. type. form = strProc);
          obj := scope. type. decl;
          WHILE (obj # NIL) & (obj. name^ # name) DO
            obj := obj. rightObj
          END
        END;
        
        IF (obj = NIL) & (scope. mode = objTBProc) &
           (scope(TBProc). receiver. name^ = name) THEN
          obj := scope(TBProc). receiver
        END
      | scope: Struct DO
        obj := scope. decl;
        WHILE (obj # NIL) & (obj. name^ # name) DO
          obj := obj. rightObj
        END;
        IF (obj = NIL) & (scope. base # NIL) THEN
          base := ResolveType (scope. base);
          IF (base. form = strRecord) THEN
            obj := FindDecl (base, name)
          END
        END
      END;
      RETURN obj
    END
  END FindDecl;

PROCEDURE Find* (currScope: Object; VAR name: ARRAY OF CHAR): Object;
(* Searches for object declared as `name', starting at `currScope' and 
   proceeding through the enclosing scopes.  *)
  VAR
    ptr: Object;
    next: Usable;
  BEGIN
    currScope := currScope;
    ptr := NIL;
    WHILE (ptr = NIL) & (currScope # NIL) DO
      ptr := FindDecl (currScope, name);
      IF (currScope. mode = objTBProc) THEN
        (* `currScope' is a type-bound procedure, its `localTo' field is 
           refering to the record it belongs to; continue search in the scope 
           of the record type *)
        next := currScope. localTo(Struct). localTo
      ELSE
        next := currScope. localTo
      END;
      IF (next = NIL) THEN
        currScope := NIL
      ELSE
        currScope := next(Object)
      END
    END;
    RETURN ptr
  END Find;

PROCEDURE GetBaseType* (tbProc: TBProc; needName: BOOLEAN): Struct;
(* note: the parser ensures that the type of the receiver is always a name *)
  VAR
    type, record: Struct;
  BEGIN
    type := ResolveType (tbProc. receiver. type);
    IF (type. form = strRecord) THEN
      record := type
    ELSE
      record := ResolveType (type. base)
    END;
    IF needName & (record. obj = NIL) THEN
      RETURN type
    ELSE
      RETURN record
    END
  END GetBaseType;


PROCEDURE BalanceTree (scope: Object);
(* Restructure the binary tree that holds `scope's declarations into a tree 
   with minimal depth.  *)
  
  PROCEDURE TransformIntoList (root: Object): Object;
  (* Takes the root of a sorted binary tree and returns a linear list built
     from the nodes of the tree.  The list is sorted like the original tree 
     and linked with `Object. rightObj'.  
     Note that this function uses stack space proportional to the depth of the
     tree `root'.  For a completely degenerated tree of declarations this is the
     number of declarations itself.  But such trees are only created if the 
     source file contains only declarations in an alphabetical sequence (or its
     reverse), and is therefore rather unlikely.  *)
    VAR
      head, ptr: Object;
    BEGIN
      IF (root = NIL) THEN
        RETURN NIL
      ELSE  (* transform left and right subtree, concatenate right+root+left *)
        head := TransformIntoList (root. leftObj);
        root. rightObj := TransformIntoList (root. rightObj);
        IF (head = NIL) THEN
          RETURN root
        ELSE
          ptr := head;
          WHILE (ptr. rightObj # NIL) DO
            ptr := ptr. rightObj
          END;
          ptr. rightObj := root;
          RETURN head
        END
      END
    END TransformIntoList;

  PROCEDURE TransformIntoTree (list: Object): Object;
  (* Takes a sorted linear list and transforms it into a binary tree.  *)
    VAR
      left, right, root: Object;
    BEGIN
      IF (list = NIL) THEN               (* empty list *)
        RETURN NIL
      ELSIF (list. rightObj = NIL) THEN  (* list with one element *)
        list. leftObj := NIL;
        RETURN list
      ELSE                               (* list has at least length of 2 *)
        (* split list into two halfes, left and right; the right half may be 
           one element longer than the left *)
        left := list;
        right := list. rightObj;
        WHILE (right. rightObj # NIL) & (right. rightObj. rightObj # NIL) DO
          left := left. rightObj;
          right := right. rightObj. rightObj
        END;
        (* here holds: `left' is the last element of the left half, 
           `left. right' the first of the right one; 
           and len(right half)-len(left half) is either one or zero *)
        root := left. rightObj;
        root. rightObj := TransformIntoTree (left. rightObj. rightObj);
        left. rightObj := NIL;
        root. leftObj := TransformIntoTree (list);
        RETURN root
      END
    END TransformIntoTree;

  BEGIN
    scope. localDecl := TransformIntoTree (TransformIntoList (scope.localDecl))
  END BalanceTree;


PROCEDURE ^ Type (type: AST.Type; scope: Object; definition: BOOLEAN): Struct;

PROCEDURE SetObject (ident: AST.IdentDef; obj: Object);
  BEGIN
    IF (ident. mark # NIL) THEN
      IF (ident. mark. str^ = "-") THEN
        INCL (obj. flags, objIsExported);
        INCL (obj. flags, objIsExportedReadOnly)
      ELSIF (ident. mark. str^ = "*") THEN
        INCL (obj. flags, objIsExported)
      END
    END;
    obj. identDef := ident;
    ident. obj := obj
  END SetObject;

PROCEDURE FormalPars (type: AST.FormalPars; pos: LONGINT; scope: Object): Struct;
  VAR
    t, ftype: Struct;
    fpsec: AST.Decl;
    name: AST.IdentDef;
    obj, last: Object;
    mode: SHORTINT;
    str: S.String;
    pos0: LONGINT;
  
  PROCEDURE AppendParam (obj: Object);
    BEGIN
      INCL (obj. flags, objIsParameter);
      obj. localTo := t;
      IF (last = NIL) THEN
        t. decl := obj
      ELSE
        last. rightObj := obj
      END;
      last := obj
    END AppendParam;
  
  BEGIN
    t := NewStruct (strProc, pos);
    type. struct := t;
    last := NIL;
    fpsec := type. fpSections;
    WHILE (fpsec # NIL) DO
      IF (fpsec(AST.FPSection). type = NIL) THEN  (* must be `...' param *)
        NEW (str, 4);
        COPY ("...", str^);
        pos0 := fpsec(AST.FPSection). name. name. pos;
        obj := NewObject (objRestParam, str, NewStruct (strUndef, pos0), pos0);
        SetObject (fpsec. name, obj);
        AppendParam (obj)
      ELSE
        ftype := Type (fpsec(AST.FPSection). type, scope, FALSE);
        IF (fpsec(AST.FPSection). var = NIL) THEN
          mode := objVar
        ELSE
          mode := objVarPar
        END;
        name := fpsec. name;
        WHILE (name # NIL) DO
          obj := NewObject (mode, name. name. str, ftype, name. name. pos);
          SetObject (name, obj);
          AppendParam (obj);
          name := name. next
        END
      END;
      fpsec := fpsec. next
    END;
    IF (type. colon = NIL) THEN
      t. SetBase (NewStruct (strNone, pos))
    ELSE
      t. SetBase (Type (type. resultType, scope, FALSE))
    END;
    RETURN t
  END FormalPars;

PROCEDURE Type (type: AST.Type; scope: Object; definition: BOOLEAN): Struct;
  VAR
    t, ftype, t0: Struct;
    expr: AST.Expr;
    fields: AST.Decl;
    name: AST.IdentDef;
    ident: AST.Ident;
    obj, dummy: Object;
    pos: LONGINT;
  BEGIN
    WITH type: AST.TypeName DO
      IF (type. qualident. module = NIL) THEN
        obj := Find (scope, type. qualident. ident. name. str^)
      ELSE
        obj := Find (scope, type. qualident. module. name. str^);
        (* if this did not get us a module reference, then the parser
           has done wrong *)
        ASSERT ((obj # NIL) & (obj. mode = objModule));
        obj := FindDecl (obj. localDecl, type. qualident. ident. name. str^)
      END;
      pos := type. qualident. ident. name. pos;
      IF (obj = NIL) OR (obj. mode # objType) THEN
        Err (pos, "Type identifier expected")
      END;
      
      IF definition THEN
        (* only create new instance of `Struct' if this is an alias 
           declaration for an existing type *)
        t := NewStruct (strName, pos);
        type. struct := t;
        t. decl := obj;
        RETURN t
      ELSE
        RETURN obj. type
      END
      
    | type: AST.Pointer DO
      t := NewStruct (strPointer, type. pointer. pos);
      type. struct := t;
      IF (type. base IS AST.TypeName) &
         (type. base(AST.TypeName). qualident. module = NIL) THEN
        ident := type. base(AST.TypeName). qualident. ident;
        obj := Find (scope, ident. name. str^);
        IF (obj = NIL) THEN  (* this is a forward reference *)
          obj := NewObject (objType, ident. name. str, 
                            NewStruct (strUndef, ident. name. pos), 
                            ident. name. pos);
          INCL (obj. flags, objIsForwardDecl);
          obj. type. obj := obj;
          dummy := InsertDecl (scope, obj)
        END;
        IF (obj. mode = objType) & (objIsForwardDecl IN obj. flags) THEN
          (* do we have a forward type by now? *)
          t. SetBase (obj. type)
        END
      END;
      IF (t. base = NIL) THEN  
        t. SetBase (Type (type. base, scope, FALSE))
      END
      
    | type: AST.ProcType DO
      t := FormalPars (type. fpars, type. procedure. pos, scope);
      type. struct := t
      
    | type: AST.Array DO
      IF (type. exprList = NIL) THEN  (* open array *)
        t := NewStruct (strOpenArray, type. array. pos);
        t0 := t
      ELSE
        t := NewStruct (strArray, type. array. pos);
        t0 := t;
        expr := type. exprList. next;
        WHILE (expr # NIL) DO
          t0. SetBase (NewStruct (strArray, type. array. pos));
          t0 := t0. base;
          expr := expr. next
        END
      END;
      type. struct := t;
      t0. SetBase (Type (type. type, scope, FALSE))
      
    | type: AST.Record DO
      t := NewStruct (strRecord, type. record. pos);
      type. struct := t;
      IF (type. base # NIL) THEN
        t. SetBase (Type (type. base, scope, FALSE));
        t0 := ResolveType (t. base);
        t0. AddExt (t)
      END;
      fields := type. fields;
      WHILE (fields # NIL) DO
        IF (fields(AST.FieldList). type # NIL) THEN
          ftype := Type (fields(AST.FieldList). type, scope, FALSE);
          name := fields. name;
          WHILE (name # NIL) DO
            obj := NewObject (objField, name. name. str, ftype, 
                              name. name. pos);
            SetObject (name, obj);
            InsertUnique (t, obj);
            name := name. next
          END
        END;
        fields := fields. next
      END
    END;
    t. localTo := scope;
    RETURN t
  END Type;


PROCEDURE ^ Body (body: AST.Body; scope: Object);

PROCEDURE ProcDecl (decl: AST.ProcDecl; scope: Object);
  VAR
    obj, prevDecl: Object;
    receiver: Struct;
    record, type: Struct;
  BEGIN
    (* parse receiver and get the procedure's base record *)
    record := NIL;
    IF (decl. receiver # NIL) THEN
      obj := NewObject (objTBProc, decl. name. name. str, NIL, 
                        decl. name. name. pos);
      SetObject (decl. name, obj);

      receiver := FormalPars (decl. receiver, decl. name. name. pos, scope);
      receiver. localTo := obj;
      obj(TBProc). receiver := receiver. decl;
      IF (receiver. decl. mode IN {objVar, objVarPar}) THEN
        type := ResolveType (receiver. decl. type);
        IF (type. form = strRecord) THEN
          record := type
        ELSIF (type. form = strPointer) & (type. base. form = strRecord) THEN
          record := ResolveType (type. base)
        END
      END;
      IF (record = NIL) THEN
        Err (receiver. decl. pos, "Illegal receiver type")
      END
    ELSE
      obj := NewObject (objProc, decl. name. name. str, NIL, 
                        decl. name. name. pos);
      SetObject (decl. name, obj)
    END;
    
    (* get formal parameter list *)
    obj. SetType (FormalPars (decl. fpars, decl. procedure. pos, scope));
    obj. type. localTo := obj;
    
    (* see if we are resolving a forward declaration *)
    IF (record # NIL) THEN
      prevDecl := FindDecl (record, obj. name^)
    ELSE
      prevDecl := FindDecl (scope, obj. name^)
    END;
    (* ignore any previous declaration if it isn't of the right form *)
    IF (prevDecl = NIL) OR (prevDecl. mode # obj. mode) OR
       ~(objIsForwardDecl IN prevDecl. flags) THEN
      prevDecl := NIL
    END;
    
    IF (prevDecl # NIL) THEN  (* resolving forward declaration *)
      (* multiple forward declaration? *)
      IF (decl. arrow # NIL) THEN
        Err (obj. pos, "Multiple forward declarations")
      END;
      INCL (obj. flags, objWasForwardDecl);
      
      (* copy procedure data into object of forward declaration *)
      prevDecl. mode := obj. mode;
      prevDecl. SetType (obj. type);
      obj. type. localTo := prevDecl;
      IF (obj. mode = objTBProc) THEN
        obj(TBProc). receiver. localTo := prevDecl;
        prevDecl(TBProc). receiver := obj(TBProc). receiver;
      END;
      prevDecl. localDecl := obj. localDecl;
      prevDecl. flags := obj. flags;
      prevDecl. pos := obj. pos;
      
      SetObject (decl. name, prevDecl);
      obj := prevDecl
    ELSE  (* proper declaration, possibly a forward declaration *)
      IF (decl. arrow # NIL) THEN
        INCL (obj. flags, objIsForwardDecl)
      END;
      IF (record # NIL) THEN  (* tb proc *)
        (* add procedure to the record's field list *)
        InsertUnique (record, obj)
      ELSE  (* insert normal procedure *)
        InsertUnique (scope, obj)
      END
    END;
    
    IF (decl. body # NIL) THEN
      Body (decl. body, obj)
    END
  END ProcDecl;

PROCEDURE ConstDecl (decl: AST.ConstDecl; scope: Object);
  VAR
    type: Struct;
    obj: Object;
  BEGIN
    type := struct[strUndef];  (* don't assign types to constants *)
    obj := NewObject (objConst, decl. name. name. str, type, 
                      decl. name. name. pos);
    SetObject (decl. name, obj);
    InsertUnique (scope, obj)
  END ConstDecl;

PROCEDURE TypeDecl (decl: AST.TypeDecl; scope: Object);
  VAR
    type, t0, ext: Struct;
    obj, prev, first: Object;
  BEGIN
    type := Type (decl. type, scope, TRUE);
    type. localTo := scope;
    obj := NewObject (objType, decl. name. name. str, type, 
                      decl. name. name. pos);
    SetObject (decl. name, obj);
    type. obj := obj;
    
    (* does a forward declared type of this name exist?  problem: the
       type we just parsed may have introduced a forward declaration, so
       we can't deal with this case when we create `obj' in the first 
       place *)
    prev := FindDecl (scope, decl. name. name. str^);
    IF (prev = NIL) OR (prev. mode # objType) OR
       ~(objIsForwardDecl IN prev. flags) THEN
      prev := NIL
    END;

    IF (prev = NIL) THEN
      IF (obj. type. obj = NIL) THEN  (* set name if type is unnamed *)
        obj. type. obj := obj
      END;
      InsertUnique (scope, obj)

    ELSE
      (* resolving forward type; here holds: `obj' holds the type 
         declaration, `prev' the old forward declaration that is 
         resolved by `obj' *)
      type := obj. type;

      (* don't insert `obj' into the scope, but rather move the relevant
         attributes of `obj' into `prev'; copy the new type into the old 
         location, adjust `localTo' field of record fields to refer to 
         `prev.type' instead of `type'; change entry in 
         `Sym.typeConstrList' to refer to `prev.type' *)
      SetObject (decl. name, prev);
      prev. type^ := type^;
      prev. type. obj := prev;
      prev. mode := obj. mode;
      INCL (prev. flags, objWasForwardDecl);
      prev. pos := obj. pos;
      IF (type. form = strRecord) THEN
        first := type. decl;
        WHILE (first # NIL) DO
          IF (first. localTo = type) THEN
            first. localTo := prev. type
          END;
          first := first. rightObj
        END;
        
        (* fix reference from base type to extension *)
        IF (type. base # NIL) THEN
          t0 := ResolveType (type. base);
          IF (t0. extList = obj. type) THEN
            t0. extList := prev. type
          ELSE
            ext := t0. extList;
            WHILE (ext. nextExt # obj. type) DO
              ext := ext. nextExt
            END;
            ext. nextExt := prev. type
          END;
          prev. type. nextExt := obj. type. nextExt
        END
      END
    END
  END TypeDecl;

PROCEDURE VarDecl (decl: AST.VarDecl; scope: Object);
  VAR
    type: Struct;
    ident: AST.IdentDef;
    obj: Object;
  BEGIN
    type := Type (decl. type, scope, FALSE);
    ident := decl. name;
    WHILE (ident # NIL) DO
      obj := NewObject (objVar, ident. name. str, type, ident. name. pos);
      SetObject (ident, obj);
      InsertUnique (scope, obj);
      ident := ident. next
    END
  END VarDecl;

PROCEDURE Body (body: AST.Body; scope: Object);
  VAR
    decl: AST.Decl;
  BEGIN
    decl := body. declSeq;
    WHILE (decl # NIL) DO
      IF (decl. name # NIL) THEN
        WITH decl: AST.ProcDecl DO
          ProcDecl (decl, scope)
        | decl: AST.ConstDecl DO
          ConstDecl (decl, scope)
        | decl: AST.TypeDecl DO
          TypeDecl (decl, scope)
        | decl: AST.VarDecl DO
          VarDecl (decl, scope)
        END
      END;
      decl := decl. next
    END
  END Body;

PROCEDURE ScanModule (module: AST.Module; symTabCache: Object): Module;
  VAR
    mobj: Module;
    import: AST.Decl;
  
  PROCEDURE AddImport (import: AST.Import; scope: Object);
    VAR
      iobj, symTab: Object;
      mname: AST.Ident;
    BEGIN
      iobj := NewObject (objModule, import. name. name. str, NIL, 
                         import. name. name. pos);
      SetObject (import. name, iobj);
      InsertUnique (scope, iobj);
      
      (* locate symbol table of imported module and store it in 
         `iobj.localDecl' *)
      mname := import. module;
      IF (mname. name. str^ = "SYSTEM") THEN
        symTab := system
      ELSE
        symTab := symTabCache;
        WHILE (symTab # NIL) & (symTab. name^ # mname. name. str^) DO
          symTab := symTab. rightObj
        END;
        IF (symTab = NIL) THEN
          Err (mname. name. pos, "No symbol table for this module, try --closure")
        END
      END;
      iobj. localDecl := symTab
    END AddImport;
  
  BEGIN
    mobj := NewModule (module. name. name. str^, module, 
                       module. name. name. pos);
    SetObject (module. name, mobj);
    IF (module. importList # NIL) THEN
      import := module. importList. imports;
      WHILE (import # NIL) DO
        AddImport (import(AST.Import), mobj);
        import := import. next
      END
    END;
    Body (module.  body, mobj);
    RETURN mobj
  END ScanModule;

PROCEDURE FixSuperLinks (module: AST.Module);
  VAR
    decl: AST.Decl;
    obj: TBProc;
    super: Object;
    record: Struct;
  
  PROCEDURE GetModule (u: Usable): Module;
    BEGIN
      WHILE ~(u IS Module) DO
        u := u. localTo
      END;
      RETURN u(Module)
    END GetModule;
  
  BEGIN
    IF (module. body # NIL) THEN
      decl := module. body. declSeq;
      WHILE (decl # NIL) DO
        IF (decl IS AST.ProcDecl) & (decl(AST.ProcDecl). receiver # NIL) THEN
          obj := decl. name. obj(TBProc);
          record := GetBaseType (obj, FALSE);
          IF (record. base # NIL) THEN
            super := FindDecl (record. base, obj. name^);
            IF (super # NIL) & (super. mode = objTBProc) &
               ((objIsExported IN super. flags) OR
                (GetModule (super) = GetModule (obj))) THEN
              obj. super := super(TBProc)
            END
          END
        ELSE
        END;
        decl := decl. next
      END
    END
  END FixSuperLinks;

PROCEDURE CreateSymTab* (module: AST.Module; imports: Object): Module;
(* Creates the symbol table for the abstract syntax tree `module'.  `imports'
   is a list of symbol tables of modules that might be imported by `module';
   the list is linked with `Object.rightObj'.  If `module' imports a module
   that isn't part of `imports', or a declaration refers to an unknown object,
   the procedure will abort the program with an error message.  *)
  VAR
    mobj: Module;
  BEGIN
    currModule := module;
    mobj := ScanModule (module, imports);
    currModule := NIL;
    FixSuperLinks (module);
    RETURN mobj
  END CreateSymTab;

PROCEDURE RemoveLocal* (mobj: Module; clearIdenfDef: BOOLEAN);
(* Removes (most) declarations local to the module from the symbol table.
   With `clearIdentDef', all links from the symbol table to the AST are
   removed.  *)
  
  PROCEDURE ClearIdentDef (obj: Object);
    PROCEDURE ClearIdentDefStruct (struct: Struct);
      VAR
        member: Object;
      BEGIN  (* this proc may cross module boundaries *)
        IF (struct # NIL) &
           ((struct. obj = NIL) OR (struct. obj = obj)) THEN
          ClearIdentDefStruct (struct. base);
          IF (struct. form = strRecord) THEN
            member := struct. decl;
            WHILE (member # NIL) DO
              ClearIdentDef (member);
              member := member. rightObj
            END
          END
        END
      END ClearIdentDefStruct;
    
    BEGIN
      IF (obj # NIL) THEN
        IF (obj. mode = objModule) THEN
          obj. identDef := NIL
        ELSE
          ClearIdentDef (obj. leftObj);
          ClearIdentDef (obj. rightObj);
          obj. identDef := NIL;
          IF (obj IS TBProc) THEN
            ClearIdentDef (obj(TBProc). receiver)
          END
        END;
        IF (obj. type # NIL) THEN
          ClearIdentDefStruct (obj. type)
        END
      END
    END ClearIdentDef;
  
  PROCEDURE ScanTree (obj: Object);
    BEGIN
      IF (obj # NIL) THEN
        ScanTree (obj. leftObj);
        ScanTree (obj. rightObj);
        
        IF (obj. mode = objProc) OR (obj. mode = objTBProc) THEN
          obj. localDecl := NIL
        END
      END
    END ScanTree;
  
  BEGIN
    IF clearIdenfDef THEN
      ClearIdentDef (mobj)
    END;
    ScanTree (mobj. localDecl)
  END RemoveLocal;



PROCEDURE Reverse* (modList: Object): Object;
  VAR
    new, mod: Object;
  BEGIN
    new := NIL;
    WHILE (modList # NIL) DO
      mod := modList;
      modList := modList. rightObj;
      mod. rightObj := new;
      new := mod
    END;
    RETURN new
  END Reverse;


PROCEDURE InitPredef;
(* Place predefined types and procedures into the top most scope. *)
  VAR
    new, dummy: Object;
    str: S.String;
  CONST
    valueParam = 1;
    varParam = 2;
    restParam = 3;

  PROCEDURE PredefStruct (scope: Object; name: ARRAY OF CHAR; form: SHORTINT);
  (* Create predefined type `name' with form `form'.  Place a reference to
     the type structure in `struct[form]'. *)
    VAR
      obj, dummy: Object;
      str: S.String;
    BEGIN
      NEW (str, Strings.Length (name)+1);
      COPY (name, str^);
      obj := NewObject (objType, str, NIL, S.undefPos); 
      INCL (obj. flags, objIsExported);  (* object is always visible *)
      IF (struct[form] = NIL) THEN
        obj. SetType (NewStruct (form, S.undefPos));
        struct[form] := obj. type;
        obj. type. obj := obj
      ELSE
        obj. type := struct[form]
      END;
      dummy := InsertDecl (scope, obj)
    END PredefStruct;

  PROCEDURE PredefProc (scope: Object; name: ARRAY OF CHAR; p0, p1, p2: SHORTINT);
  (* Create predefined procedure `name' with identification `id'.  The 
     procedure's parameter list is set to the types p0, p1, p2, and the result
     type to `res'. *)
    VAR
      obj, dummy: Object;
      str: S.String;
    
    PROCEDURE CreateParam (VAR param: Object; class: SHORTINT);
      VAR
        mode: SHORTINT;
      BEGIN
        (* value or variable parameter? *)
        CASE class OF
        | varParam:
          mode := objVarPar
        | valueParam:
          mode := objVar
        | restParam:
          mode := objRestParam
        END;
        (* create parameter object (it won't have a name) *)
        param := NewObject (mode, str, NewStruct (strUndef, S.undefPos),
                            S.undefPos);
        INCL (param. flags, objIsParameter)
      END CreateParam;
      
    BEGIN
      NEW (str, Strings.Length (name)+1);
      COPY (name, str^);
      obj := NewObject (objProc, str, NIL, S.undefPos);
      INCL (obj. flags, objIsExported);
      (* create parameter list *)
      obj. SetType (NewStruct (strProc, S.undefPos));
      IF (p0 # 0) THEN
        CreateParam (obj. type. decl, p0);
        IF (p1 # 0) THEN
          CreateParam (obj. type. decl. rightObj, p1);
          IF (p2 # 0) THEN
            CreateParam (obj. type. decl. rightObj. rightObj, p2)
          END
        END
      END;
      dummy := InsertDecl (scope, obj)
    END PredefProc;
  
  BEGIN
    predef := NewModule ("_predef_", NIL, S.undefPos);

    (* predefined (and named) types *)
    PredefStruct (predef, "BOOLEAN", strBoolean);
    PredefStruct (predef, "CHAR", strChar);
    PredefStruct (predef, "LONGCHAR", strLongChar);
    PredefStruct (predef, "SHORTINT", strShortInt);
    PredefStruct (predef, "INTEGER", strInteger);
    PredefStruct (predef, "LONGINT", strLongInt);
    PredefStruct (predef, "HUGEINT", strHugeInt);
    PredefStruct (predef, "REAL", strReal);
    PredefStruct (predef, "LONGREAL", strLongReal);
    PredefStruct (predef, "SET", strSet32);
    (* implicit types *)
    struct[strUndef] := NewStruct (strUndef, S.undefPos);
    struct[strUndef]. base := struct[strUndef];
    struct[strStringConst] := NewStruct (strStringConst, S.undefPos);
    struct[strNone] := NewStruct (strNone, S.undefPos);
    struct[strNil] := NewStruct (strNil, S.undefPos);

    PredefProc (predef, "ABS", valueParam, 0, 0);
    PredefProc (predef, "ASH", valueParam, valueParam, 0);
    PredefProc (predef, "ASSERT", valueParam, valueParam, 0);
    PredefProc (predef, "CAP", valueParam, 0, 0);
    PredefProc (predef, "CHR", valueParam, 0, 0);
    PredefProc (predef, "COPY", valueParam, varParam, 0);
    PredefProc (predef, "DEC", varParam, valueParam, 0);
    PredefProc (predef, "ENTIER", valueParam, 0, 0);
    PredefProc (predef, "EXCL", varParam, valueParam, 0);
    PredefProc (predef, "HALT", valueParam, 0, 0);
    PredefProc (predef, "INC", varParam, valueParam, 0);
    PredefProc (predef, "INCL", varParam, valueParam, 0);
    PredefProc (predef, "LEN", valueParam, valueParam, 0);
    PredefProc (predef, "LONG", valueParam, 0, 0);
    PredefProc (predef, "LONGCHR", valueParam, 0, 0);
    PredefProc (predef, "MAX", valueParam, 0, 0);
    PredefProc (predef, "MIN", valueParam, 0, 0);
    PredefProc (predef, "NEW", varParam, restParam, 0);
    PredefProc (predef, "ODD", valueParam, 0, 0);
    PredefProc (predef, "ORD", valueParam, 0, 0);
    PredefProc (predef, "SHORT", valueParam, 0, 0);
    PredefProc (predef, "SIZE", valueParam, 0, 0);
    
    (* boolean constants *)
    NEW (str, 6);
    COPY ("FALSE", str^);
    new := NewObject (objConst, str, struct[strBoolean], S.undefPos);
    dummy := InsertDecl (predef, new);
    NEW (str, 5);
    COPY ("TRUE", str^);
    new := NewObject (objConst, str, struct[strBoolean], S.undefPos);
    dummy := InsertDecl (predef, new);
    BalanceTree (predef);
    
    (* pseudo module SYSTEM *)
    system := NewModule ("SYSTEM", NIL, S.undefPos);
    PredefStruct (system, "BYTE", strByte);
    PredefStruct (system, "PTR", strPtr);
    PredefStruct (system, "SET8", strSet8);
    PredefStruct (system, "SET16", strSet16);
    PredefStruct (system, "SET32", strSet32);
    PredefStruct (system, "SET64", strSet64);
    PredefStruct (system, "ADDRESS", strAddress);
    PredefProc (system, "ADR", varParam, 0, 0);
    PredefProc (system, "BIT", valueParam, valueParam, 0);
    PredefProc (system, "GET", valueParam, varParam, 0);
    PredefProc (system, "LSH", valueParam, valueParam, 0);
    PredefProc (system, "MOVE", valueParam, valueParam, 0);
    PredefProc (system, "NEW", varParam, valueParam, 0);
    PredefProc (system, "PUT", valueParam, varParam, 0);
    PredefProc (system, "ROT", valueParam, valueParam, 0);
    PredefProc (system, "VAL", valueParam, valueParam, 0);
    BalanceTree (system)
  END InitPredef;

BEGIN
  predef := NIL;
  system := NIL;
  InitPredef
END CNSymTab.
