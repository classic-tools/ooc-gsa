(* 	$Id: SymbolTable.Mod,v 1.61 1999/05/18 15:45:48 acken Exp $	 *)
MODULE SymbolTable;
(*  Creates and maintains the symbol table.
    Copyright (C) 1995-1999  Michael van Acken

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
  Strings, Strings2, IntStr, E := Error, D := Data, StdTypes, StdPragmas;
  
CONST
  (* The following constants define identifiers for the standard predefined and
     SYSTEM procedures *)
  (* conversions *)
  predCHR* =12; predLONGCHR* =13; predENTIER*=14; predLONG* =15; predORD* =16;
  predSHORT* =17;
  (* some constants *)
  predMAX* =18; predMIN* =19; predSIZE* =20;
  (*  monadic operators *)
  predABS* =21; predCAP* =22; predODD* =23; sysADR* =24;
  (* binary operators *)
  predASH* =26; sysBIT* =27; sysLSH* =28; sysROT* =29; 
  predLEN* =30; sysVAL* =31;
  (* assignment variations *)
  predINCL* =32; predEXCL* =33; predINC* =34; predDEC* =35; predCOPY* =36;
  sysMOVE* =37;  sysGET* =38; sysPUT* =39;
  sysNEW* =42;   predNEW* =43;  (* predNEW+1 must be left free *)
  (* traps *)
  predHALT* =45; predASSERT*=46;
  
  predFirstFree* = 47;  (* first usable proc id for back-end *)

TYPE
  StructList* = POINTER TO StructListDesc;
  StructListDesc* = RECORD
    next-: StructList;
    type*: D.Struct
  END;



CONST
  globalLevel* = 0;
  currentModuleId* = 0;
  predefModuleId* = -1;
  systemModuleId* = -2;

VAR
  predef-: D.Object;
  (* this visibility scope declares the predefined constants, types, functions,
     and procedures; it is lowest possible scope *)
  system-: D.Object;
  (* the predefined module SYSTEM *)
  mod*: D.Object;
  (* this is the root of the currently compiled module's symbol table; this
     variable is only valid for the front-end, ie while `ParseDecl.Module' is
     running, otherwise it is NIL; `ParseDecl.Module' returns the data that is
     accumulated here in a variable parameter *)
  currScope-: D.Object;
  (* the starting point when searching for an identifier and the point where
     `Insert' places new objects *)
  typeConstrList*: StructList;
  (* This list contains all RECORD and ARRAY constructors (anonymous or named)
     of the current module. This means the list enumerates all types that may 
     have to be modeled into a type descriptor.*)

  tbProcCounter: LONGINT;
  (* used to create index values for type-bound procedures whose true index
     can only be determined after the whole module has been parsed *)
  
  importedMods*: D.Object;
  (* this list contains all modules imported with `SymbolFile.Read', the 
     modules are linked with `Object.rightObj' *)
     
  constTrue-, constFalse-: D.Const;
  (* boolean constants *)

  mem-: D.Object;
  (* pseudo variable $mem, used to model `wild' memory accesses and 
     assignments *)
  store*: D.Object;
  (* pseudo variable $store, used to model alias effects when assigning to
     variable parameters, nonlocal variables, and heap objects *)

  paramsMatchExt*: PROCEDURE (str1, str2: D.Struct): BOOLEAN;
  (* here the back-end can install an additional predicate to check whether two
     formal parameter lists match; this procedure checks additional criteria 
     like calling convention and parameter passing rules and is used by the
     ParamMatch procedure below; it is usually defined in the SystemFlags 
     module *)


PROCEDURE NewStruct* (form: SHORTINT; pos: LONGINT): D.Struct;
  VAR
    str: D.Struct;
  BEGIN
    NEW (str);
    D.InitStruct (str, form, pos);
    RETURN str
  END NewStruct;

PROCEDURE NewObject*(name: ARRAY OF CHAR; mode: SHORTINT; pos: LONGINT): D.Object;
  VAR
    obj: D.Object;
  BEGIN
    NEW (obj);
    D.InitObject (obj, name, mode, pos);
    IF (currScope # NIL) THEN
      obj. level := currScope. level
    END;
    RETURN obj
  END NewObject;

PROCEDURE NewModule* (modName: ARRAY OF CHAR; pos: LONGINT): D.Object;
(* Allocate memory for module, initialize it.  The module name is stored in
   `mod. name' and `mod. data(Data.Const). string'.  *)
  VAR
    mod: D.Object;
    const: D.Const;
  BEGIN
    mod := NewObject (modName, D.objModule, pos);
    mod. localTo := predef;
    NEW (const);
    D.InitConst (const, NIL);
    const. string := mod. name;
    mod. data := const;
    RETURN mod
  END NewModule;

PROCEDURE GetBoolConst* (bool: BOOLEAN): D.Const;
(* Returns the constant object representing the value of `bool'.  *)
  BEGIN
    IF bool THEN
      RETURN constTrue
    ELSE
      RETURN constFalse
    END
  END GetBoolConst;


PROCEDURE LocalObject* (ref: D.Object; obj: D.Object): BOOLEAN;
(* Result is TRUE iff `obj' is defined in the same module as `ref'.  *)
  BEGIN
    RETURN (ref. moduleId = obj. moduleId)
  END LocalObject;

PROCEDURE ImportedObject* (ref: D.Object; obj: D.Object): BOOLEAN;
(* Result is TRUE iff `obj' is imported from another module than `ref'.  *)
  BEGIN
    RETURN (obj. moduleId # predefModuleId) & (obj. moduleId # ref. moduleId)
  END ImportedObject;

PROCEDURE Visible* (ref: D.Object; obj: D.Object): BOOLEAN;
(* Result is TRUE iff `obj' is visible in the module that defines `ref'.  *)
  BEGIN
    RETURN (ref. moduleId = obj. moduleId) OR
           (D.objIsExported IN obj. flags)
  END Visible;

PROCEDURE Unnamed* (t: D.Struct): BOOLEAN;
(* Result is TRUE iff the type `t' isn't associated with a type name.  *)
  BEGIN
    RETURN (t. obj = NIL)
  END Unnamed;

PROCEDURE LocalType* (ref: D.Object; t: D.Struct): BOOLEAN;
(* Result is TRUE iff `Unnamed (t)' or `t. obj' is declared in the same module
   as `ref'. 
   Note: This function fails if `t' is an unnamed subtype of an imported type,
     since it would declare this type as local. *)
  BEGIN
    RETURN Unnamed (t) OR LocalObject (ref, t. obj)
  END LocalType;

PROCEDURE Module* (obj: D.Object): D.Object;
(* Find module that declares `obj'.  *)
  VAR
    scope: D.Object;
  BEGIN
    IF (obj. moduleId = systemModuleId) THEN
      RETURN system
    ELSIF (obj. moduleId = predefModuleId) THEN
      RETURN predef
    ELSIF (mod # NIL) & (mod. moduleId = obj. moduleId) THEN
      RETURN mod
    ELSE
      scope := importedMods;
      WHILE (scope # NIL) & (scope. moduleId # obj. moduleId) DO
        scope := scope. rightObj
      END;
      RETURN scope
    END
  END Module;

PROCEDURE NumberOfTBProcs* (record: D.Struct; baseComplete: BOOLEAN): LONGINT;
(* Determines the number of type-bound procedures defined in `record',
   excluding any type-bound procedures with a negative index.  If the exact
   number is not known yet, return -1.
   pre: `(record = NIL) OR (record. form = D.strRecord)'  *)
  VAR
    obj: D.Object;
    count: LONGINT;
  BEGIN
    IF (record = NIL) THEN
      RETURN 0
    ELSIF (record. base # NIL) & ~baseComplete & 
          (Module (record. base. obj) = mod) THEN
      (* if this is an extended record, whose base type is defined in the
         current module, then assume that additional type-bound procedures
         can be added to the base type during compilation of this module;
         setting `baseComplete' to TRUE overrides this *)
      RETURN -1
    ELSE
      count := NumberOfTBProcs (record. base, baseComplete);
      obj := record. decl;
      WHILE (obj # NIL) DO  
        IF (obj. mode = D.objTBProc) & (obj. offset >= count) THEN
          count := obj. offset+1
        END;
        obj := obj. rightObj
      END;
      RETURN count
    END
  END NumberOfTBProcs;


PROCEDURE TypeName* (VAR descr: ARRAY OF CHAR; str: D.Struct);
(* Get a plain text type description for a structure. *)
  VAR
    elemDescr: ARRAY 512 OF CHAR;
    num: ARRAY 32 OF CHAR;
    m: D.Object;
  BEGIN
    IF (str. obj # NIL) THEN (* named type *)
      IF (mod # NIL) & ImportedObject (mod, str. obj) THEN
        m := Module (str. obj);
        COPY (m. name^, descr);
        Strings2.AppendChar (".", descr)
      ELSE
        COPY ("", descr)
      END;
      Strings.Append (str. obj. name^, descr)
    ELSE
      CASE str. form OF
      | D.strArray, D.strOpenArray: 
        IF (str. form = D.strArray) THEN
          COPY ("ARRAY ", descr);
          IntStr.IntToStr (str. len, num);
          Strings.Append (num, descr);
          Strings.Append (" OF ", descr)
        ELSE
          COPY ("ARRAY OF ", descr)
        END;
        TypeName (elemDescr, str. base);
        Strings.Append (elemDescr, descr)
      | D.strNil: COPY ("NIL", descr)
      | D.strNone: COPY ("void", descr)
      | D.strPointer: COPY ("POINTER", descr)
      | D.strProc: COPY ("PROCEDURE", descr)
      | D.strStringConst8: COPY ("StringConst8", descr)
      | D.strStringConst16: COPY ("StringConst16", descr)
      | D.strRecord: COPY ("RECORD", descr)
      | D.strUndef: COPY ("undef", descr)
      
      (* groups of types used to describe the predefined procedures *)
      | D.grpChar: COPY ("character", descr)
      | D.grpInteger: COPY ("integer", descr)
      | D.grpReal: COPY ("real", descr)
      | D.grpNumeric: COPY ("numeric", descr)
      | D.grpComplex: COPY ("complex", descr)
      | D.grpSet: COPY ("set", descr)
      | D.grpString8: COPY ("string8", descr)
      | D.grpString16: COPY ("string16", descr)
      | D.grpAnyString: COPY ("string", descr)
      | D.grpArray: COPY ("array", descr)
      | D.grpCharArray: COPY ("character array", descr)
      | D.grpPointer: COPY ("POINTER", descr)
      | D.grpProc: COPY ("PROCEDURE", descr)
      | D.grpPtr: COPY ("pointer", descr)
      | D.grpLong: COPY ("parameter types of LONG", descr)
      | D.grpShort: COPY ("parameter types of SHORT", descr)
      | D.grpNilCompat: COPY ("nil compatible", descr)
      | D.grpShift: COPY ("integer, CHAR, or BYTE", descr)
      | D.grpGetPut: COPY ("basic", descr)
      | D.grpAnyType: COPY ("any", descr)
      ELSE
        COPY ("", descr)
      END
    END
  END TypeName;

PROCEDURE ErrT1* (pos: LONGINT; num: INTEGER; t1: D.Struct);
(* If `t1' is no `strUndef', then print error message `num' with a textual 
   representation of type `t1' inserted instead of the `%'.  `t1' is set to
   `strUndef'.  *)
  VAR
    ins: ARRAY 512 OF CHAR;
  BEGIN
    IF (t1. form # D.strUndef) THEN
      TypeName (ins, t1);
      E.ErrIns (pos, num, ins)
    END
  END ErrT1;


PROCEDURE FindDecl* (scope: D.Addressable; name: ARRAY OF CHAR): D.Object;
(* Finds the declaration `name' in the visibility scope `scope'.  If no such
   declaration exists, NIL is returned.  Note: The returned object may not
   be visible in the current module.
   pre: `scope IS Object' with `scope. mode IN {objModule, objProc, 
     objTBProc}, or `scope IS Struct' with `scope. form = strRecord' *)
  VAR
    obj: D.Object;
  BEGIN
    IF (scope = NIL) THEN
      RETURN NIL
    ELSE
      WITH scope: D.Object DO
        obj := scope. localDecl;
        WHILE (obj # NIL) & (obj. name^ # name) DO
          IF (name < obj. name^) THEN
            obj := obj. leftObj
          ELSE
            obj := obj. rightObj
          END
        END
      | scope: D.Struct DO
        obj := scope. decl;
        WHILE (obj # NIL) & (obj. name^ # name) DO
          obj := obj. rightObj
        END;
        IF (obj = NIL) & (scope. base # NIL) & 
           (scope. base. form = D.strRecord) THEN
          obj := FindDecl (scope. base, name)
        END
      END;
      RETURN obj
    END
  END FindDecl;

PROCEDURE BaseDefinition* (receiver: D.Object; name: ARRAY OF CHAR): D.Object;
(* Finds the type-bound procedure `name' defined in one of `receiver's base
   types, or returns NIL if no such procedure exists or if the procedure isn't
   visible in the current module.  *)
  VAR
    str: D.Struct;
    obj: D.Object;
  BEGIN
    str := receiver. type;               (* this is the receiver's type *)
    IF (str. form = D.strPointer) THEN (* get corresponding record type *)
      str := str. base
    END;
    IF (str. form = D.strRecord) THEN
      obj := FindDecl (str. base, name);
      IF (obj # NIL) & Visible (receiver, obj) THEN
        RETURN obj
      ELSE
        RETURN NIL
      END
    ELSE
      RETURN NIL
    END
  END BaseDefinition;

PROCEDURE InsertDecl (scope: D.Addressable; obj: D.Object): D.Object;
(* Inserts `obj' into `scope'.  If no declaration `obj. name^' exists, result 
   is NIL.  Otherwise nothing is inserted and the previous declaration of that
   name is returned. 
   pre: `scope IS Object' with `scope. mode IN {objModule, objProc, 
     objTBProc}, or `scope IS Struct' with `scope. form = strRecord' *)
  VAR
    base: D.Object;
    
  PROCEDURE InsertInTree (VAR tree: D.Object): D.Object;
    VAR
      ptr: D.Object;
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

  PROCEDURE InsertInList (VAR list: D.Object): D.Object;
    VAR
      ptr: D.Object;
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
    obj. moduleId := currScope. moduleId;
    obj. level := currScope. level;
    WITH scope: D.Object DO
      RETURN InsertInTree (scope. localDecl)
    | scope: D.Struct DO
      IF (obj. mode = D.objTBProc) THEN  
        (* inserting type-bound procedure: set procedure index *)
        base := BaseDefinition (obj. data(D.Object), obj. name^);
        IF (base # NIL) THEN             (* redefinition, use old index *)
          obj. offset := base. offset
        ELSE                             (* new proc, add unique index *)
          obj. offset := NumberOfTBProcs (scope, FALSE);
          IF (obj. offset < 0) THEN
            DEC (tbProcCounter);
            obj. offset := tbProcCounter
          END
        END
      END;
      RETURN InsertInList (scope. decl)
    END
  END InsertDecl;


PROCEDURE OpenScope* (scope: D.Object; moduleId, level: INTEGER);
(* Push `scope' onto the scope stack.  *)
  BEGIN
    scope. localDecl := NIL;
    scope. moduleId := moduleId;
    scope. level := level;
    currScope := scope;
    IF (level = globalLevel) THEN
      tbProcCounter := 0
    END
  END OpenScope;

PROCEDURE CloseScope* (check: BOOLEAN);
(* Does some checks on the current scope if `check=TRUE', removes top element
   from scope stack.  *)
  CONST
    setMarker = 0;
    clearIfExported = 1;
    acceptMarker = 2;
    objMarker = D.objIsInitialized;  (* reuse flag with no meaning for procs *)
  VAR
    str: StructList;
    str0: D.Struct;
    obj, proc, obj0: D.Object;
    index: LONGINT;
    
  PROCEDURE UnresolvedForward (obj: D.Object);
  (* Searches subtree `obj' for unresolved forward type and procedure 
     declarations. *)
    BEGIN
      IF (obj # NIL) THEN
        IF (D.objIsForwardDecl IN obj. flags) THEN
          E.Err (obj. pos, 300)          (* unresolved forward declaration *)
        END; 
        UnresolvedForward (obj. leftObj);
        UnresolvedForward (obj. rightObj)
      END
    END UnresolvedForward;
  
  PROCEDURE WarnUnused (obj: D.Object);
  (* Searches subtree `obj' for declarations that where never used as 
     identifiers.  Record fields are also considered.
     Restriction: Type declarations of the form 
       TYPE Ptr = POINTER TO PtrDesc; PtrDesc = RECORD a: Ptr END;
     use both type A and B, so it won't be detected if both A and B are never
     used again in the source code. *)
    VAR
      ptr: D.Object;
    BEGIN
      IF (obj # NIL) & LocalObject (currScope, obj) THEN
        IF ~(D.objIsUsed IN obj. flags) &
           ~(D.objIsParameter IN obj. flags) &
           ~((obj. mode = D.objTBProc) & 
             (BaseDefinition (obj. data(D.Object), obj. name^) # NIL)) THEN
          (* warn that `obj' is never used and not exported, unless
              a) it's a parameter 
              b) it's a type-bound procedure that redefines another one *)
          E.Err (obj. pos, -420)         (* warning: unused object *)
        END;
        
        IF (obj. mode = D.objType) & (obj. type. form = D.strRecord) THEN
          (* scan record for unused record fields or type-bound procedures *)
          ptr := obj. type. decl;
          WHILE (ptr # NIL) DO
            IF ~(D.objIsUsed IN obj. flags) THEN
              E.Err (obj. pos, -420)     (* warning: unused object *)
            END;
            ptr := ptr. rightObj
          END
        END;
        
        WarnUnused (obj. leftObj);
        WarnUnused (obj. rightObj)
      END
    END WarnUnused;
  
  PROCEDURE GetTBProc (record: D.Struct; index: LONGINT): D.Object;
    VAR
      obj: D.Object;
    BEGIN
      WHILE (record # NIL) DO
        obj := record. decl;
        WHILE (obj # NIL) DO  (* loop through fields/tb procs *)
          IF (obj. mode = D.objTBProc) & (obj. offset = index) THEN
            RETURN obj
          END;
          obj := obj. rightObj
        END;
        record := record. base
      END;
      RETURN NIL
    END GetTBProc;
  
  PROCEDURE SetTBProcFlags (record: D.Struct; mode: SHORTINT);
    VAR
      obj: D.Object;
    BEGIN
      obj := record. decl;
      WHILE (obj # NIL) DO
        IF (obj. mode = D.objTBProc) THEN
          CASE mode OF
          | setMarker:
            INCL (obj. flags, objMarker)
          | clearIfExported:
            IF (D.objIsExported IN obj. flags) THEN
              EXCL (obj. flags, objMarker)
            END
          | acceptMarker:
            IF (objMarker IN obj. flags) THEN
              INCL (obj. flags, D.objFinalTBProc);
              EXCL (obj. flags, objMarker)
            END
          END
        END;
        obj := obj. rightObj
      END
    END SetTBProcFlags;
  
  BEGIN
    UnresolvedForward (currScope. localDecl);
    
    IF (currScope = mod) THEN
      (* fix index entries for type-bound procedures; because a records base
         type is declared before the record itself, a simple linear scan
         through `typeConstrList' is sufficient to fix all `offset' fields *)
      str := typeConstrList;
      WHILE (str # NIL) DO  (* loop through type descriptor candidates *)
        IF (str. type. form = D.strRecord) THEN
          index := NumberOfTBProcs (str. type. base, TRUE);
          obj := str. type. decl;
          WHILE (obj # NIL) DO
            IF (obj. mode = D.objTBProc) & (obj. offset < 0) THEN
              proc := BaseDefinition (obj. data(D.Object), obj. name^);
              IF (proc # NIL) THEN
                obj. offset := proc. offset
              ELSE
                obj. offset := index;
                INC (index)
              END
            END;
            obj := obj. rightObj
          END;
          
          SetTBProcFlags (str. type, setMarker)
        END;
        str := str. next
      END;
      
      (* set the `objFinalTBProc' flag for type-bound procedures that are not 
         redefined in the current module, and which cannot possibly redefined
         in another module due to the lack of the necessary export marks *)
      str := typeConstrList;
      WHILE (str # NIL) DO  (* loop through type descriptor candidates *)
        IF (str. type. form = D.strRecord) THEN
          IF (D.structIsExported IN str. type. flags) THEN
            str0 := str. type;
            WHILE (str0 # NIL) DO
              SetTBProcFlags (str0, clearIfExported);
              str0 := str0. base
            END
          END;
          
          obj := str. type. decl;
          WHILE (obj # NIL) DO
            IF (obj. mode = D.objTBProc) THEN
              obj0 := BaseDefinition (obj. data(D.Object), obj. name^);
              WHILE (obj0 # NIL) & (obj0. Module() = mod) DO
                EXCL (obj0. flags, objMarker);
                obj0 := BaseDefinition (obj0. data(D.Object), obj. name^)
              END
            END;
            obj := obj. rightObj
          END
        END;
        str := str. next
      END;
      
      str := typeConstrList;
      WHILE (str # NIL) DO  (* loop through type descriptor candidates *)
        IF (str. type. form = D.strRecord) THEN
          SetTBProcFlags (str. type, acceptMarker)
        END;
        str := str. next
      END;
    END;
    
    IF check THEN  (* check for semantic errors *)
      IF (currScope = mod) THEN
        (* search for unresolved forward type-bound procedures *)
        str := typeConstrList;
        WHILE (str # NIL) DO  (* loop through type descriptor candidates *)
          IF (str. type. form = D.strRecord) THEN
            obj := str. type. decl;
            WHILE (obj # NIL) DO  (* loop through fields/tb procs *)
              IF (obj. mode = D.objTBProc) & 
                 (D.objIsForwardDecl IN obj. flags) THEN
                E.Err (obj. pos, 300)      (* unresolved forward declaration *)
              END;
              obj := obj. rightObj
            END;
            
            IF ~(D.structAbstractType IN str. type. flags) THEN
              (* scan all type-bound procs for active "abstract" *)
              FOR index := 0 TO NumberOfTBProcs (str. type, TRUE)-1 DO
                proc := GetTBProc (str. type, index);
                IF (proc # NIL) & (D.objAbstractTBProc IN proc. flags) THEN
                  E.ErrIns (str. type. pos, 451, proc. name^)
                  (* some tb proc is still abstract *)
                END
              END
            END
          END;
          str := str. next
        END
      END;
      WarnUnused (currScope. localDecl)
    END;
    
    IF (currScope. mode IN {D.objProc, D.objTBProc}) THEN
      (* adjust level for procedure; this assigns to global procedures a level
         of 0 (=Sym.globalLevel) *)
      DEC (currScope. level)
    END;
    IF (currScope. localTo # NIL) & (currScope. localTo IS D.Object) THEN
      currScope := currScope. localTo(D.Object)
    ELSE  (* closing type-bound procedure *)
      currScope := mod
    END
  END CloseScope;

PROCEDURE GlobalDecl* (obj: D.Object): BOOLEAN;
(* Returns TRUE iff `obj' is declared on module level.  Note that this is
   equivalent to `obj.level = globalLevel' _after_ the parser has finished
   his job.  During parsing this is not true.  *)
  BEGIN
    RETURN (obj. mode = D.objTBProc) OR
           (obj. localTo IS D.Object) & 
             (obj. localTo(D.Object). mode = D.objModule)
  END GlobalDecl;




PROCEDURE TransformIntoList* (root: D.Object): D.Object;
(* Takes the root of a sorted binary tree and returns a linear list built
   from the nodes of the tree.  The list is sorted like the original tree 
   and linked with `Object. rightObj'.  
   Note that this function uses stack space proportional to the depth of the
   tree `root'.  For a completely degenerated tree of declarations this is the
   number of declarations itself.  But such trees are only created if the 
   source file contains only declarations in an alphabetical sequence (or its
   reverse), and is therefore rather unlikely.  *)
  VAR
    head, ptr: D.Object;
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

PROCEDURE TransformIntoTree* (list: D.Object): D.Object;
(* Takes a sorted linear list and transforms it into a binary tree.  *)
  VAR
    left, right, root: D.Object;
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

PROCEDURE BalanceTree* (scope: D.Object);
(* Restructure the binary tree that holds `scope's declarations into a tree 
   with minimal depth.  *)
  BEGIN
    scope. localDecl := TransformIntoTree (TransformIntoList (scope.localDecl))
  END BalanceTree;



PROCEDURE SameType* (a, b: D.Struct): BOOLEAN;
(* Result is TRUE iff `a' and `b' denote the same type.  See Oberon-2 report, 
   Appendix A.  This function also returns TRUE if one of the types is faulty;
   this suppresses any successive error messages regarding these types.  *)
  BEGIN
    RETURN (a = b) & (a. form # D.strOpenArray) OR
           (a. form = D.strUndef) OR (b. form = D.strUndef)
  END SameType;

PROCEDURE ^ ParamsMatch* (str1, str2: D.Struct; 
                          allowResultExt: BOOLEAN): BOOLEAN;

PROCEDURE EqualTypes* (a, b: D.Struct): BOOLEAN;
(* Result is TRUE iff `a' and `b' denote equal types.  See Oberon-2 report,
   Appendix A.  *)
  BEGIN
    RETURN SameType (a, b) OR
           (a. form = D.strOpenArray) & (b. form = D.strOpenArray) & 
             EqualTypes (a. base, b. base) OR
           (a. form = D.strProc) & (b. form = D.strProc) & 
             ParamsMatch (a, b, FALSE)
 END EqualTypes;

PROCEDURE ExtensionOf* (a, b: D.Struct): BOOLEAN;
(* Result is TRUE iff the type `a' is an extension of the type `b'.  See
   Oberon-2 report, Appendix A.  *)
  BEGIN
    (* if `a' and `b' are pointers: reduce them to their base types *)
    IF (a.form = D.strPointer) & (b.form = D.strPointer) THEN
      a := a. base; b := b. base
    END;
    IF (a.form = D.strRecord) & (b.form = D.strRecord) THEN
      (* either `a' and `b' where records from the start, or they were both
         record pointers *)
      WHILE (a # NIL) & (a. form = D.strRecord) DO 
        IF SameType (a, b) THEN
          RETURN TRUE
        ELSE
          a := a. base
        END
      END
    END;
    RETURN FALSE
  END ExtensionOf;

PROCEDURE ParameterType* (param: D.Object): D.Struct;
(* Returns the type of parameter `param', taking the effects of a WITH 
   statement into account.
   pre: D.objIsParameter IN param.flags  *)
  BEGIN
    IF (D.objIsTwisted IN param. flags) & (param. localDecl # NIL) THEN
      (* formal parameter type was changed by an enclosing WITH statement;
         use instead the type of `param.localDecl', which WITH kindly set for
         us (in non-conformant mode) to refer to an object with the old type *)
      RETURN param. localDecl. type
    ELSE
      RETURN param. type
    END
  END ParameterType;

PROCEDURE ParamsMatch* (str1, str2: D.Struct;
                        allowResultExt: BOOLEAN): BOOLEAN;
(* Result is TRUE iff the formal parameter lists `a' and `b' match.  See 
   Oberon-2 report, Appendix A.  When `allowResultExt' is set, the result is
   additionally TRUE if the result types are not the same, but the result of
   `str1' is a pointer type extending the result type of `str2'.
   Addtional compatibilty tests of back-end specific flags (calling convention,
   special parameters) are done in StdTypes.ParamsMatchExt.
   pre: `str1. mode = strProc' and `str2. mode = strProc' *)
  VAR
    p0, p1: D.Object;
  BEGIN
    p0 := str1. decl; p1 := str2. decl;
    WHILE (p0 # NIL) & (p1 # NIL) DO
      IF (p0. mode # p1. mode) OR 
         ~EqualTypes (ParameterType (p0), ParameterType (p1)) THEN
        RETURN FALSE
      END;
      p0 := p0. rightObj; p1 := p1. rightObj
    END;
    (* make sure that both lists have the same length, that the result type are
       compatible, and that the back-end doesn't complain *)
    RETURN (p0 = p1) & 
           (SameType (str1. base, str2. base) OR
            allowResultExt &
              (str1. base. form = D.strPointer) &
              ExtensionOf (str1. base, str2. base)) &
           ((paramsMatchExt = NIL) OR paramsMatchExt (str1, str2))
  END ParamsMatch;
  
PROCEDURE TypeInGroup* (t: D.Struct; group: SHORTINT): BOOLEAN;
(* Determine if type `t' is part of a given set of types. *)
  VAR
    f: SHORTINT;
  BEGIN
    f := t. form;
    IF (f >= D.grpInteger) THEN
      (* groups of types don't fit into any group *)
      RETURN FALSE
    END;
    CASE group OF
    | D.strPointer .. D.strRecord:
      RETURN FALSE
    | D.grpChar:
      RETURN (f = D.strChar8) OR (f = D.strChar16)
    | D.grpInteger:
      RETURN (D.strShortInt <= f) & (f < D.strReal)
    | D.grpReal:
      RETURN (f = D.strReal) OR (f = D.strLongReal)
    | D.grpNumeric:
      RETURN (D.strShortInt <= f) & (f < D.strComplex)
    | D.grpComplex:
      RETURN (f = D.strComplex) OR (f = D.strLongComplex)
    | D.grpSet:
      RETURN (D.strSet8 <= f) & (f < D.strByte)
    | D.grpString8:
      RETURN (t. form = D.strStringConst8) OR 
             TypeInGroup (t, D.grpArray) & (t. base. form = D.strChar8)
    | D.grpString16:
      RETURN (t. form = D.strStringConst16) OR 
             TypeInGroup (t, D.grpArray) & (t. base. form = D.strChar16)
    | D.grpAnyString:
      RETURN TypeInGroup (t, D.grpCharArray) OR
             TypeInGroup (t, D.grpStringConst)
    | D.grpStringConst:
      RETURN (f = D.strStringConst8) OR (f = D.strStringConst16)
    | D.grpArray:
      RETURN (f = D.strArray) OR (f = D.strOpenArray)
    | D.grpCharArray: 
      RETURN TypeInGroup (t, D.grpArray) & TypeInGroup (t. base, D.grpChar)
    | D.grpPointer:
      RETURN (f = D.strPointer)
    | D.grpProc:
      RETURN (f = D.strProc)
    | D.grpPtr:
      RETURN (f = D.strPointer) OR (f = D.strPtr)
    | D.grpStructured:
      RETURN TypeInGroup (t, D.grpArray) OR (f = D.strRecord) OR
             TypeInGroup (t, D.grpComplex) OR TypeInGroup (t, D.grpStringConst)
    | D.grpLong:
      RETURN (D.strShortInt <= f) & (f <= D.strInteger) OR
             (f = D.strReal) OR
             (f = D.strComplex) OR
             (D.strSet8 <= f) & (f <= D.strSet16) OR
             (StdPragmas.targetInteger. value >= 64) & 
               ((f = D.strLongInt) OR (f = D.strSet32)) OR
             (f = D.strChar8) OR
             (f = D.strStringConst8)
    | D.grpShort:
      RETURN (D.strInteger <= f) & (f <= D.strHugeInt) OR 
             (f = D.strLongReal) OR
             (f = D.strLongComplex) OR 
             (D.strSet16 <= f) & (f <= D.strSet64) OR
             (f = D.strChar16) OR
             (f = D.strStringConst16)
    | D.grpNilCompat:
      RETURN (f = D.strNil) OR (f = D.strPointer) OR (f = D.strPtr) OR
             (f = D.strProc)
    | D.grpShift:
      RETURN TypeInGroup (t, D.grpInteger) OR 
             (f IN {D.strChar8, D.strChar16, D.strByte})
    | D.grpGetPut:
      RETURN (D.strBoolean <= f) & (f <= D.strPtr) &
               ~TypeInGroup (t, D.strComplex) OR 
             (f = D.strPointer) OR (f = D.strProc)
    | D.grpAnyType:
      RETURN TRUE
    ELSE
      RETURN (f = group)
    END
  END TypeInGroup;

PROCEDURE Includes* (a, b: D.Struct; grp: SHORTINT): BOOLEAN;
(* TRUE iff `a' and `b' are types from group `grp' and `a' includes `b'.  *)
  BEGIN
    RETURN TypeInGroup (a, grp) & TypeInGroup (b, grp) & (a. form >= b. form)
  END Includes;




PROCEDURE Insert* (obj: D.Object);
(* Inserts the object into the local scope `currScope'.  If an object with
   same name already exists in the local scope, an error will be reported. *)
  VAR
    old: D.Object;
  BEGIN
    old := InsertDecl (currScope, obj);
    IF (old # NIL) THEN  (* object with the same name already exists *)
      E.Err (obj. pos, 301)           (* multiple declaration of same name *)
    END
  END Insert;

PROCEDURE InsertParams* (proc: D.Object);
(* Inserts copies of the parameter list (and the receiver) of the procedure 
   declaration type `proc' into the local scope, ie `currScope'.
   pre: proc. mode IN {objProc, objTBProc} *)
  VAR
    param, copy: D.Object;
  BEGIN
    IF (proc. mode = D.objTBProc) THEN  (* insert receiver *)
      NEW (copy);
      copy^ := proc. data(D.Object)^;
      Insert (copy);
      copy. data := proc. data(D.Object)
    END;
    (* insert each of the formal parameters *)
    param := proc. type. decl;
    WHILE (param # NIL) DO
      NEW (copy);
      copy^ := param^;
      Insert (copy);
      copy. data := param;
      param := param. rightObj
    END;
  END InsertParams;

PROCEDURE MakeFormalParsLocal* (proc: D.Object);
(* Sets `localTo' field of `proc's formal parameters and receiver to `proc'. *)
  VAR
    fpar: D.Object;
  BEGIN
    IF (proc. mode = D.objTBProc) THEN
      proc. data(D.Object). localTo := proc
    END;
    IF (proc. type. decl # NIL) THEN
      fpar := proc. type. decl;
      REPEAT
        fpar. localTo := proc;
        fpar := fpar. rightObj
      UNTIL (fpar = NIL)
    END
  END MakeFormalParsLocal;

PROCEDURE Find* (name: ARRAY OF CHAR): D.Object;
(* Searches for object declared as `name', starting at `currScope' and 
   proceeding through the enclosing scopes.  *)
  VAR
    ptr: D.Object;
    scope: D.Addressable;
  BEGIN
    ptr := NIL;
    scope := currScope;
    WHILE (ptr = NIL) & (scope # NIL) DO
      ptr := FindDecl (scope, name);
      IF (scope(D.Object). mode = D.objTBProc) THEN
        (* `scope' is a type-bound procedure, its `localTo' field is refering
           to the record it belongs to; continue search at module level *)
        scope := mod
      ELSE
        scope := scope(D.Object). localTo
      END
    END;
    IF (ptr # NIL) THEN
      INCL (ptr. flags, D.objIsUsed)
    END;
    RETURN ptr
  END Find;

PROCEDURE FindField* (record: D.Struct; name: ARRAY OF CHAR): D.Object;
(* Locates field or type-bound procedure `name' visible in `record'.  If `name'
   can't be found in `record' the search proceeds to its base type(s).  Only
   objects visible in the current module are returned.  A result of NIL means
   that either no such field/tb proc is declared, or that it isn't exported by
   the type that declares it.  *)
  VAR
    ptr: D.Object;
  BEGIN
    ptr := NIL;
    WHILE (record # NIL) & (ptr = NIL) DO
      ptr := FindDecl (record, name);
      record := record. base
    END;
    IF (ptr = NIL) OR ~Visible (mod, ptr) THEN
      RETURN NIL
    ELSE
      INCL (ptr. flags, D.objIsUsed);
      RETURN ptr
    END
  END FindField;
  
PROCEDURE InsertField* (record: D.Struct; obj: D.Object);
(* Inserts the object into `record's scope.  If an object with same name 
   already exists in the local scope, an error will be reported. *)
  VAR
    old: D.Object;
    ins: ARRAY 256 OF CHAR;
  BEGIN
    old := InsertDecl (record, obj);
    IF (old # NIL) THEN  (* object with the same name already exists *)
      E.Err (obj. pos, 301)             (* multiple declaration of same name *)
    ELSIF (obj. mode = D.objField) & (record. base # NIL) THEN
      old := FindField (record. base, obj. name^);
      IF (old # NIL) THEN
        TypeName (ins, old. localTo(D.Struct));
        E.ErrIns (obj. pos, 309, ins)
      END
    END
  END InsertField;


PROCEDURE InitPredef;
(* Place predefined types and procedures into the top most scope. *)
  VAR
    new: D.Object;

  PROCEDURE PredefStruct (name: ARRAY OF CHAR; form: SHORTINT);
  (* Create predefined type `name' with form `form'.  Place a reference to
     the type structure in `struct[form]'. *)
    VAR
      obj: D.Object;
    BEGIN
      obj := NewObject (name, D.objType, D.undefPos); 
      INCL (obj. flags, D.objIsExported);  (* object is always visible *)
      IF (D.struct[form] = NIL) THEN
        obj. type := NewStruct (form, D.undefPos);
        D.struct[form] := obj. type;
        StdTypes.StructAlloc (obj. type);  (* set alignment and size *)
        obj. type. obj := obj
      ELSE
        obj. type := D.struct[form]
      END;
      Insert (obj)
    END PredefStruct;

  PROCEDURE PredefProc (name: ARRAY OF CHAR; id, p0, p1, p2, res: SHORTINT);
  (* Create predefined procedure `name' with identification `id'.  The 
     procedure's parameter list is set to the types p0, p1, p2, and the result
     type to `res'. *)
    VAR
      obj: D.Object;
      
    PROCEDURE CreateParam (VAR param: D.Object; form: SHORTINT);
      VAR
        mode: SHORTINT;
      BEGIN
        (* value or variable parameter? *)
        IF (form < 0) THEN
          mode := D.objVarPar
        ELSE
          mode := D.objVar
        END;
        (* create paramter object (it won't have a name) *)
        param := NewObject ("", mode, D.undefPos);
        INCL (param. flags, D.objIsParameter);
        form := ABS (form);
        IF (form < D.strNone) THEN       (* simple, unstructured type *)
          param. type := D.struct[form]
        ELSE                             (* a group of types *)
          param. type := NewStruct (form, D.undefPos)
        END
      END CreateParam;
      
    BEGIN
      obj := NewObject (name, D.objProc, D.undefPos);
      obj. data := D.GetIntConst (id, D.struct[D.strShortInt]);
      INCL (obj. flags, D.objIsExported);
      (* create parameter list *)
      obj. type := NewStruct (D.strProc, D.undefPos);
      IF (p0 # D.strNone) THEN
        CreateParam (obj. type. decl, p0);
        IF (p1 # D.strNone) THEN
          CreateParam (obj. type. decl. rightObj, p1);
          IF (p2 # D.strNone) THEN
            CreateParam (obj. type. decl. rightObj. rightObj, p2)
          END
        END        
      END;
      obj. type. base := D.struct[res];
      Insert (obj)
    END PredefProc;
  
  BEGIN
    predef := NewModule ("_predef_", D.undefPos);
    OpenScope (predef, predefModuleId, globalLevel);

    (* predefined (and named) types *)
    PredefStruct ("BOOLEAN", D.strBoolean);
    PredefStruct ("CHAR", D.strChar8);
    PredefStruct ("LONGCHAR", D.strChar16);
    PredefStruct ("SHORTINT", D.strShortInt);
    PredefStruct ("INTEGER", D.strInteger);
    PredefStruct ("LONGINT", D.strLongInt);
    IF (StdPragmas.targetInteger. value >= 64) THEN
      PredefStruct ("HUGEINT", D.strHugeInt)
    END;
    PredefStruct ("REAL", D.strReal);
    PredefStruct ("LONGREAL", D.strLongReal);
    PredefStruct ("SET", D.strSet32);
    (* implicit types *)
    D.struct[D.strUndef] := NewStruct (D.strUndef, D.undefPos);
    D.struct[D.strUndef]. base := D.struct[D.strUndef];
    D.struct[D.strUndef]. size := 1;
    D.struct[D.strStringConst8] := NewStruct (D.strStringConst8, D.undefPos);
    D.struct[D.strStringConst16] := NewStruct (D.strStringConst16, D.undefPos);
    D.struct[D.strNone] := NewStruct (D.strNone, D.undefPos);
    D.struct[D.strNil] := NewStruct (D.strNil, D.undefPos);
    D.InitConst (D.constNil, D.struct[D.strNil]);
    D.constNil. preserve := TRUE;
    D.InitConst (D.constUndef, D.struct[D.strUndef]);
    D.constUndef. preserve := TRUE;

    (* Predefined procedures and functions; these functions are identified 
       by Object.const#NIL, and Object.const.int#0 contains their function id.
       The definition includes patterns for their parameter lists; negative 
       type ids denote variable parameters. 
       The following definitions are incomplete, ie, they have to be handled
       by dedicated code:
       ABS/SIZE/ORD (result), ASSERT/INC/DEC/LEN (2nd param),
       HALT (const param), MIN/MAX (param+result), NEW  *)
    (*          name   id    1. param    2. param 3. param  result *)
    PredefProc ("ABS", predABS, D.grpNumeric, D.strNone, D.strNone, D.strUndef);
    PredefProc ("ASH", predASH, D.grpInteger, D.grpInteger, D.strNone, D.strLongInt);
    PredefProc ("ASSERT", predASSERT, D.strBoolean, D.grpInteger, D.strNone, D.strNone);
    PredefProc ("CAP", predCAP, D.grpChar, D.strNone, D.strNone, D.strUndef);
    PredefProc ("CHR", predCHR, D.grpInteger, D.strNone, D.strNone, D.strChar8);
    PredefProc ("COPY", predCOPY, D.grpAnyString, -D.grpCharArray, D.strNone, D.strNone);
    PredefProc ("DEC", predDEC, -D.grpInteger, D.strUndef, D.strNone, D.strNone);
    PredefProc ("ENTIER", predENTIER, D.grpReal, D.strNone, D.strNone, D.strLongInt);
    PredefProc ("EXCL", predEXCL, -D.grpSet, D.grpInteger, D.strNone, D.strNone);
    PredefProc ("HALT", predHALT, D.grpInteger, D.strNone, D.strNone, D.strNone);
    PredefProc ("INC", predINC, -D.grpInteger, D.strUndef, D.strNone, D.strNone);
    PredefProc ("INCL", predINCL, -D.grpSet, D.grpInteger, D.strNone, D.strNone);
    PredefProc ("LEN", predLEN, D.grpArray, D.grpInteger, D.strNone, D.strLongInt);
    PredefProc ("LONG", predLONG, D.grpLong, D.strNone, D.strNone, D.strUndef);
    PredefProc ("LONGCHR", predLONGCHR, D.grpInteger, D.strNone, D.strNone, D.strChar16);
    PredefProc ("MAX", predMAX, D.strUndef, D.strNone, D.strNone, D.strUndef);
    PredefProc ("MIN", predMIN, D.strUndef, D.strNone, D.strNone, D.strUndef);
    PredefProc ("NEW", predNEW, -D.grpPointer, D.strNone, D.strNone, D.strNone);
    PredefProc ("ODD", predODD, D.grpInteger, D.strNone, D.strNone, D.strBoolean);
    PredefProc ("ORD", predORD, D.grpChar, D.strNone, D.strNone, D.strUndef);
    PredefProc ("SHORT", predSHORT, D.grpShort, D.strNone, D.strNone, D.strUndef);
    PredefProc ("SIZE", predSIZE, D.strUndef, D.strNone, D.strNone, D.strUndef);
    
    (* boolean constants *)
    new := NewObject ("FALSE", D.objConst, D.undefPos);
    constFalse := D.GetIntConst (0, D.struct[D.strBoolean]); 
    constFalse. preserve := TRUE;
    new. data := constFalse;
    new. type := D.struct[D.strBoolean];
    Insert (new);
    new := NewObject ("TRUE", D.objConst, D.undefPos);
    constTrue := D.GetIntConst (1, D.struct[D.strBoolean]);
    constTrue. preserve := TRUE;
    new. data := constTrue;
    new. type := D.struct[D.strBoolean];
    Insert (new);
    currScope := NIL;
    BalanceTree (predef);
    
    (* pseudo module SYSTEM *)
    system := NewModule ("SYSTEM", D.undefPos);
    OpenScope (system, systemModuleId, globalLevel);

    PredefStruct ("BYTE", D.strByte);
    PredefStruct ("PTR", D.strPtr);
    PredefStruct ("SET8", D.strSet8);
    PredefStruct ("SET16", D.strSet16);
    PredefStruct ("SET32", D.strSet32);
    IF (StdPragmas.targetInteger. value >= 64) THEN
      PredefStruct ("SET64", D.strSet64)
    END;
    PredefStruct ("ADDRESS", D.strAddress);
    
    (* The following definitions are incomplete, i.e., they have to be handled
       by dedicated code: LSH/ROT/VAL (fix result type) *)
    (*          name   id    1. param    2. param 3. param  result *)
    PredefProc ("ADR", sysADR, -D.grpAnyType, D.strNone, D.strNone, D.strAddress);
    PredefProc ("BIT", sysBIT, D.strAddress, D.grpInteger, D.strNone, D.strBoolean);
    PredefProc ("GET", sysGET, D.strAddress, -D.grpGetPut, D.strNone, D.strNone);
    PredefProc ("LSH", sysLSH, D.grpShift, D.grpInteger, D.strNone, D.strUndef);
    PredefProc ("MOVE", sysMOVE, D.strAddress, D.strAddress, D.grpInteger, D.strNone);
    PredefProc ("NEW", sysNEW, -D.grpPtr, D.grpInteger, D.strNone, D.strNone);
    PredefProc ("PUT", sysPUT, D.strAddress, D.grpGetPut, D.strNone, D.strNone);
    PredefProc ("ROT", sysROT, D.grpShift, D.grpInteger, D.strNone, D.strUndef);
    PredefProc ("VAL", sysVAL, D.strUndef, D.grpAnyType, D.strNone, D.strUndef);

    currScope := NIL;
    BalanceTree (system);
    
    mem := NewObject ("$mem", D.objUndef, D.undefPos);
    mem. type := D.struct[D.strUndef];
    store := NewObject ("$store", D.objUndef, D.undefPos);
    store. type := D.struct[D.strUndef]
  END InitPredef;


PROCEDURE AddStructRef* (VAR list: StructList; type: D.Struct);
  BEGIN
    IF (list = NIL) THEN
      NEW (list);
      list. next := NIL;
      list. type := type
    ELSIF (list. type # type) THEN
      AddStructRef (list. next, type)
    END
  END AddStructRef;

PROCEDURE Init*;
(* Must be called before every compilation.
   pre: `structSize' is set by the back-end.  *)
  BEGIN
    IF (predef = NIL) THEN
      InitPredef
    END;
    currScope := predef;
    typeConstrList := NIL
  END Init;
  
BEGIN
  currScope := NIL;
  predef := NIL;
  importedMods := NIL;
  constTrue := NIL;
  constFalse := NIL;
  mem := NIL;
  store := NIL;
  paramsMatchExt := NIL
END SymbolTable.

