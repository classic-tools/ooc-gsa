(* 	$Id: ParseDecl.Mod,v 1.73 1999/06/17 18:15:57 acken Exp $	 *)
MODULE ParseDecl;
(*  Parses Oberon-2 declarations and module, builds symbol table.
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
  Strings, Parameter, Filenames, 
  E := Error, S := Scanner, D := Data, StdTypes, CodeGen, Sym := SymbolTable, 
  SymbolFile, Attr := Attributes, Expr := ParseExpr, Statm := ParseStatm, 
  Opc := Opcode, SystemFlags, GuardCond, UndefVar, CopyPropagation, 
  DeadCodeElimination, StdPragmas;


CONST
  (* values for `exp' parameter of procedures `DeclSeq' and `Type' *)
  noExport = 0;  
  noReadOnlyExport = 1;
  anyExport = noReadOnlyExport+1;
  
  (* type restrictions that are passed to `Type': *)
  typeIsParameter = 0;
  (* if the type has no name, it has to be an open array or a procedure type *)
  typeIsReceiver = 1;
  (* the type has to be a named record or a pointer to record *)
  typeIsResult = 2; 
  (* the type has to be legal as a function's result *)
  typeIsPointerBase = 3; 
  (* the type has to be a legal pointer base type *)
  typeNotOpenArray = 4; 
  (* the type can't be an open array *)
  typeNotAbstract = 5;
  (* the type must not be a record declared as "abstract" *)
  
  
VAR
  removeDeadCode*: BOOLEAN;
  (* if TRUE, then run copy propagation and dead code elimination on the
     module's and every procedure's greg *)
  
  moduleData: CodeGen.Module;
  (* used to store symbol table and code fragments of the module *)
  
     
PROCEDURE SkipModifiers (VAR scanState: S.ScanState; VAR modifiers: BOOLEAN);
(* If the scanner is looking at the starting `[' of a sequence of system flags,
   store the current scanner state in `scanState' and set `modifiers' to TRUE.
   Otherwise return FALSE in `modifiers'.  *)
  BEGIN
    IF (S.sym = S.lBrak) THEN
      modifiers := TRUE;
      S.SaveScanPos (scanState);
      WHILE (S.sym # S.rBrak) & (S.sym # S.endOfFile) DO
        S.GetSym
      END;
      S.GetSym
    ELSE
      modifiers := FALSE
    END
  END SkipModifiers;


PROCEDURE ^ Type (restr: SET; exp: SHORTINT): D.Struct;

PROCEDURE FormalPars (VAR fpars: D.Struct);
(* Reads a formal parameter list and returns its value as a type structure.  
   The parameter names are checked for double declarations.
   post: If current token is not "(", then the parameter list is considered to
     be empty (no parameters and no function result). Otherwise the parameters
     inside the enclosing parenthesis are parsed, possibly followed by the
     function's result type. *)
  VAR
    first, last, obj: D.Object;
    mode: SHORTINT;
    resynch: BOOLEAN;

  PROCEDURE RestParam (read: BOOLEAN): BOOLEAN;
    BEGIN
      RETURN (D.structEnableRestParam IN fpars. flags) & S.ThreeDots (read)
    END RestParam;

  BEGIN
    (* initialize `fpar' with an empty parameter list *)
    fpars := Sym.NewStruct (D.strProc, S.currSymPos);
    fpars. base := D.struct[D.strNone];
    SystemFlags.StructModifiers (fpars, TRUE);
    IF (S.sym = S.lParen) THEN
      (* list of formal parameters exists (even if it is empty) *)
      S.GetSym;
      IF (S.sym = S.var) OR (S.sym = S.ident) OR RestParam (FALSE) THEN
        (* parameter list is not empty *)
        last := NIL;
        resynch := FALSE;
        LOOP
          IF RestParam (TRUE) THEN
            (* generic rest parameter `...' *)
            obj := Sym.NewObject ("...", D.objRestParam, S.currSymPos);
            INCL (obj. flags, D.objIsParameter);
            obj. type := D.struct[D.strNone];
            IF (last = NIL) THEN
              fpars. decl := obj
            ELSE
              last. rightObj := obj
            END;
            S.GetSym;
            EXIT

          ELSE  (* formal parameter section *)
            (* First check if the identifier list is preceded by a VAR
               modifier.  Set mode accordingly. *)
            IF (S.sym = S.var) THEN
              mode := D.objVarPar;
              S.GetSym
            ELSE
              mode := D.objVar
            END;

            (* Read list of identifiers and create an object for each entry.
               `first' and `last' mark the head/tail of the object list. *)
            first := last;
            LOOP
              (* Parse identifiers seperated by a comma.  A missing comma marks
                 the end of the list.  `last' keeps track of last identifier
                 in list.  Objects are concatenated via field `obj.right'. *)
              IF (S.sym = S.ident) THEN
                (* Create new object, link the very first one to `fpars' and
                   keep count of the parameters in fpars.len *)
                IF (last = NIL) THEN
                  last := Sym.NewObject (S.str^, mode, S.currSymPos);
                  fpars. decl := last
                ELSE
                  last. rightObj := Sym.NewObject (S.str^, mode, S.currSymPos);
                  last := last. rightObj
                END;
                INCL (last. flags, D.objIsParameter);
                S.GetSym;
                SystemFlags.ObjectModifiers (last, TRUE)
              ELSE
                E.Err (S.currSymPos, 100); (* identifier expected *)
                S.GetSym;
                WHILE (S.sym # S.rParen) & (S.sym # S.end) &
                      (S.sym < S.begin) DO  (* try to resync symbol stream *)
                  S.GetSym
                END;
                resynch := TRUE
              END;
              IF (S.sym # S.comma) & (S.sym # S.ident) OR resynch THEN
                EXIT
              END;
              S.CheckSym (S.comma)
            END; (* loop *)
            IF resynch THEN
              (* leave loop if an error disrupted the symbol stream  *)
              EXIT
            END;

            (* Read type declaration following the identifiers. *)
            S.CheckSym (S.colon);
            last. type := Type ({typeIsParameter}, noExport);
            (* set the type and mnolev for each identifier in the (partial) 
               parameter list *)
            IF (first = NIL) THEN
              first := fpars. decl
            ELSE
              first := first. rightObj
            END;
            last. rightObj := NIL;
            WHILE (first # NIL) DO
              first. type := last. type;
              first. moduleId := Sym.currScope. moduleId;
              first. level := Sym.currScope. level+1;
              SystemFlags.ObjectModifiers (first, FALSE);
              first := first. rightObj
            END;
            IF (S.sym # S.semicolon) & (S.sym # S.ident) &
               (S.sym # S.var) & (S.sym # S.upto) THEN
              EXIT
            END;
            S.CheckSym (S.semicolon)
          END
        END
      END;
      S.CheckSym (S.rParen);

      IF (S.sym = S.colon) THEN
        (* formal parameters describe a real function: parse result type *)
        S.GetSym;
        fpars. base := Type ({typeIsResult}, noExport)   (* read result type *)
      END
    END;
    
    (* check that no two parameters have the same name *)
    last := fpars. decl;
    WHILE (last # NIL) DO
      obj := fpars. decl;
      WHILE (obj # last) & (obj. name^ # last. name^) DO
        obj := obj. rightObj
      END;
      IF (obj # last) THEN
        E.Err (last. pos, 301)  (* multiple declaration of same name *)
      END;
      last := last. rightObj
    END;
    SystemFlags.StructModifiers (fpars, FALSE);
    
    StdTypes.StructAlloc (fpars)
  END FormalPars;


PROCEDURE IdentDef (obj: D.Object; mode: SHORTINT; exp: SHORTINT): D.Object;
(* Reads a single identifier, possibly marked for export with `-' or `*'.  The
   name (resp the export mark) may be followed by an external declaration.
   pre: `mode' contains the new object's value for `obj.mode', `exp' determines
     whether an export mark is allowed or not (values: noExport, anyExport,
     noReadOnlyExport).  The current token has to be an identifier.
     If `obj # NIL', then no new object is allocated, but rather the given one
     reused.
   post: A new object of the class `mode' is created (or the original one in
     `obj' recycled) and returned as result, its export mark set accordingly.
   side: For `obj # NIL' and `mode IN {D.objProc, D.objTBProc}' an error is
     emitted if the export marks differ.  *)
  VAR
    prev: D.Object;
    prevExport: BOOLEAN;
  BEGIN
    prev := obj;
    IF (obj = NIL) THEN
      obj := Sym.NewObject (S.str^, mode, S.currSymPos);
      prevExport := FALSE
    ELSE
      prevExport := (D.objIsExported IN obj. flags);
      obj. flags := obj. flags-{D.objIsExported, D.objIsExportedReadOnly};
      obj. pos := S.currSymPos
    END;
    IF (mode = D.objVar) & StdPragmas.initialize. true THEN
      INCL (obj. flags, D.objIsInitialized)
    END;
    S.GetSym;
    IF (S.sym = S.times) OR (S.sym = S.minus) THEN
      IF (exp <= noExport) THEN
        E.Err (S.currSymPos, 200)  (* export only on level 0 possible *)
      ELSIF (exp = noReadOnlyExport) & (S.sym = S.minus) THEN
        E.Err (S.currSymPos, 201)  (* only export with `*' possible *)
      END;
      obj. flags := obj. flags+{D.objIsExported, D.objIsUsed, D.objIsUsedNonlocal};
      IF (S.sym = S.minus) THEN
        INCL (obj. flags, D.objIsExportedReadOnly)
      END;
      S.GetSym
    END;
    IF (prev # NIL) & (prev. mode IN {D.objProc, D.objTBProc}) &
       (prevExport # (D.objIsExported IN obj. flags)) THEN
      E.Err (obj. pos, 222)
      (* export mark differs from forward declaration *)
    END;
    RETURN obj
  END IdentDef;

PROCEDURE IdentList (VAR first, last: D.Object; mode: SHORTINT; exp: SHORTINT);
(* Reads a list of identifiers seperated by comma.
   pre: Same conditions as for IdentDef.
   post: `first' is the head of the object list, `last' its last element.  The
     elements are linked via `Object.right'.  *)
  BEGIN
    first := IdentDef (NIL, mode, exp);
    last := first;
    SystemFlags.ObjectModifiers (first, TRUE);
    LOOP
      IF (S.sym = S.comma) THEN
        S.GetSym
      ELSIF (S.sym = S.ident) THEN
        E.Err (S.lastSymEnd, 119)        (* `,' expected *)
      ELSE
        EXIT
      END;
      IF (S.sym = S.ident) THEN
        last. rightObj := IdentDef (NIL, mode, exp);
        last := last. rightObj;
        SystemFlags.ObjectModifiers (last, TRUE)
      ELSE
        E.Err (S.currSymPos, 100);  (* identifier expected *)
        S.GetSym
      END
    END
  END IdentList;

PROCEDURE Type (restr: SET; exp: SHORTINT): D.Struct;
(* Parses a type description and handles the problem of forward declared types.
   pre: `exp = noExport' forbids export of record fields, otherwise it is
     allowed.
   post: The resulting type structure is returned in `t', its file position
     in `pos'.  If no valid type could be read, the pseudo type
     `D.struct[D.strUndef]' is returned. *)
  VAR
    obj, first, last: D.Object;
    pos, p0: LONGINT;    
    t: D.Struct;
    modifiers: BOOLEAN;
    modifierScan: S.ScanState;
    
  PROCEDURE CheckRestrictions (t: D.Struct; restr: SET);
    BEGIN
      IF (typeIsParameter IN restr) & Sym.Unnamed (t) &
         (t. form # D.strOpenArray) & (t. form # D.strProc) THEN
        E.Err (pos, 203)      (* can't use type constructor here *)
      END;
      IF (typeIsReceiver IN restr) & 
         ~((t. form = D.strRecord) OR 
           (t. form = D.strPointer) & (t. base. form = D.strRecord)) THEN
        E.Err (pos, 204)      (* receiver has to be (ptr to) record *)
      END;
      IF (typeIsResult IN restr) THEN
        IF ~((D.strBoolean <= t. form) & (t. form <= D.strPtr)) & 
           (t. form # D.strPointer) & (t. form # D.strProc) THEN
          E.Err (pos, 205)    (* illegal type for function result *)
        ELSIF Sym.Unnamed (t) THEN
          E.Err (pos, 206)    (* can't use type constructor here *)
        END
      END;
      IF (typeIsPointerBase IN restr) & ~Sym.TypeInGroup (t, D.grpArray) & 
         (t. form # D.strRecord) & (t. form # D.strUndef) THEN
        E.Err (pos, 207)      (* illegal pointer base type *)
      END;
      IF (typeNotOpenArray IN restr) & (t. form = D.strOpenArray) THEN
        E.Err (pos, 208)      (* can't use open array here *)
      END;
      IF (typeNotAbstract IN restr) & (D.structAbstractType IN t. flags) THEN
        E.Err (pos, 450)      (* can't use abstract type here *)
      END
    END CheckRestrictions;
  
  PROCEDURE ArrayType (t: D.Struct);
  (* Read lengths of the array's dimensions.
     pre: Current token is the start of a constant expression.
     post: The complete array type is returned. *)
    VAR
      const: D.Const;
    BEGIN
      (* read array length *)
      const := Expr.ConstExpr (D.grpInteger);
      t. len := const. int;
      IF (t. len < 0) THEN
        E.Err (t. pos, 210)   (* array length has to be non-negative *)
      ELSIF (t. len = 0) THEN
        E.Err (t. pos, -418)  (* warning: defining array of size zero *)
      END; 
      IF (S.sym = S.comma) THEN         (* more dimensions follow *)
        S.GetSym;
        t. base := Sym.NewStruct (D.strArray, S.currSymPos);
        ArrayType (t. base);
        StdTypes.StructAlloc (t. base)
      ELSE                               (* read the array's base type *)
        S.CheckSym (S.of);
        t. base := Type ({typeNotOpenArray}, exp)
      END
    END ArrayType;

  BEGIN
    pos := S.currSymPos;
    IF (S.sym = S.ident) THEN            (* type identifier *)
      Expr.TypeQualident (t, pos)

    ELSIF (S.sym = S.array) THEN         (* (open) array type *)
      S.GetSym;
      SkipModifiers (modifierScan, modifiers);
      IF (S.sym = S.of) THEN
        t := Sym.NewStruct (D.strOpenArray, pos)
      ELSE
        t := Sym.NewStruct (D.strArray, pos)
      END;
      
      (* parse struct modifiers; problem: these modifiers appear before
         it can be determined whether this is a fixed size or open array *)
      IF modifiers THEN S.RestoreScanPos (modifierScan) END;
      SystemFlags.StructModifiers (t, TRUE);
      
      IF (S.sym = S.of) THEN             (* open array *)
        S.GetSym;
        t. base := Type (restr*{typeIsParameter}+{typeNotAbstract}, exp)
      ELSE                               (* `normal' array of fixed length *)
        ArrayType (t)
      END;
      SystemFlags.StructModifiers (t, FALSE);
      StdTypes.StructAlloc (t);
      Sym.AddStructRef (Sym.typeConstrList, t)   (* type descriptor hint *)

    ELSIF (S.sym = S.record) THEN  (* record type *)
      t := Sym.NewStruct (D.strRecord, S.currSymPos);
      S.GetSym;
      SystemFlags.StructModifiers (t, TRUE);
      IF (S.sym = S.lParen) THEN(* the record is an extension: read receiver *)
        S.GetSym;
        Expr.TypeQualident (t. base, p0);
        IF (t. base. form = D.strRecord) THEN
          IF (D.structNotExtensible IN t. base. flags) THEN
            E.Err (p0, 212)            (* this record cannot be extended *)
          END;
          t. len := t. base. len+1
        ELSE  (* no type or no record *)
          E.Err (p0, 213);               (* this isn't a record type *)
          t. base := NIL
        END;
        S.CheckSym (S.rParen)
      END;

      LOOP  (* loop over identifier lists *)
        IF (S.sym = S.ident) THEN
          IdentList (first, last, D.objField, exp);  (* get ident list *)
          S.CheckSym (S.colon);
          last. type := Type ({typeNotOpenArray, typeNotAbstract}, exp); 

          (* set type for all fields in the ident list and insert them into
             the record's list of fields and type-bound procedures *)
          obj := first;
          WHILE (obj # NIL) DO
            first := obj. rightObj;
            obj. type := last. type;
            obj. rightObj := NIL;
            Sym.InsertField (t, obj);
            obj := first
          END
        END;

        IF (S.sym # S.semicolon) THEN
          EXIT
        END;
        S.GetSym
      END;
      S.CheckSym (S.end);
      SystemFlags.StructModifiers (t, FALSE);
      StdTypes.StructAlloc (t);
      Sym.AddStructRef (Sym.typeConstrList, t)   (* type descriptor hint *)

    ELSIF (S.sym = S.pointer) THEN
      (* pointer type (possibly with a forward declaration) *)
      t := Sym.NewStruct (D.strPointer, S.currSymPos);
      S.GetSym;
      SystemFlags.StructModifiers (t, TRUE);
      S.CheckSym (S.to);
      IF (S.sym = S.ident) THEN
        (* first check if this is a forward declaration *)
        obj := Sym.Find (S.str^);
        IF (obj = NIL) THEN  (* no object named `S.str^' is declared *)
          (* initialize a new 'forward type' object and insert it into
             the symbol table *)
          obj := Sym.NewObject (S.str^, D.objType, S.currSymPos);
          obj. flags := obj. flags + {D.objIsForwardDecl, D.objIsUsed};
          obj. type := Sym.NewStruct (D.strUndef, S.currSymPos);
          obj. type. obj := obj;
          Sym.Insert (obj)
        END;
        IF (obj. mode = D.objType) & (D.objIsForwardDecl IN obj. flags) THEN
          (* do we have a forward type by now? *)
          t. base := obj. type;
          S.GetSym
        END
      END;
      IF (t. base = NIL) THEN
        (* no forward, but rather a `normal' pointer type declaration *)
        t. base := Type ({typeIsPointerBase}, exp);
        SystemFlags.StructModifiers (t, FALSE)
        (* note: for pointers whose base type isn't declared yet, the call to
                 StructModifiers is delayed until the base type is known *)
      END;
      StdTypes.StructAlloc (t)

    ELSIF (S.sym = S.procedure) THEN     (* procedure type *)
      S.GetSym;
      FormalPars (t)

    ELSE
      E.Err (S.currSymPos, 182);         (* data type expected *)
      t := D.struct[D.strUndef];
      S.GetSym
    END;
    IF ((S.sym < S.semicolon) OR (S.sym > S.else)) & (S.sym # S.rParen) THEN
      (* unexpected symbol (has to be out of follow (Type)) *)
      E.Err (S.currSymPos, 180);
      t := D.struct[D.strUndef];
      WHILE ((S.sym < S.ident) OR (S.sym > S.else)) & (* skip token *)
            (S.sym < S.begin) & (S.sym # S.rParen) DO
        S.GetSym
      END
    END;
    IF (t. form # D.strUndef) THEN
      CheckRestrictions (t, restr)
    END;
    RETURN t
  END Type;


PROCEDURE FinishRegion (greg: D.GlobalRegion; VAR exitInfo: Attr.ExitInfo);
  BEGIN
    UndefVar.CheckVars (greg, exitInfo);     (* also calculates `GuardCond' *)
    (* get rid of the NIL constant and replace it by a LONGINT value of 0; this
       leaves copy instructions in the code with a result type `NIL', but these
       are removed 3 lines later *)
    D.constNil. ReplaceUses (D.GetIntConst (0, D.struct[D.strAddress]));
    (* if a trap may occur in the procedure, mark its enter instruction as
       `instrNotDead', signalling that every call of this procedure should set
       the same flags *)
    IF exitInfo. trapped THEN
      INCL (greg. enter. flags, D.instrNotDead)
    END;
    IF removeDeadCode THEN
      DeadCodeElimination.Eliminate (greg, FALSE);
      CopyPropagation.Propagate (greg);
      GuardCond.RemoveDeadReferences (greg)  (* adapt `GuardCond' to dce *)
    END
  END FinishRegion;

PROCEDURE DeclSeq (exp: SHORTINT);
(* Parse sequence of declarations.
   pre: `exp = anyExport' allows export of identifiers, `exp <= noExport' 
     disables it.
   post: The parsed declarations are inserted into the current scope.  *)
  VAR
    obj, first, last, prev: D.Object;
    type: D.Struct; 
    greg: D.GlobalRegion;
    structList: Sym.StructList;

  PROCEDURE ProcDecl;
    VAR
      mode, rmode, oldSym: SHORTINT;
      proc, base, receiver, prevDecl: D.Object;
      prevContent: D.ObjectDesc;
      record: D.Struct;
      forward: BOOLEAN;
      exitInfo: Attr.ExitInfo;
      modifiers: BOOLEAN;
      modifierScan, modifierEnd: S.ScanState;

    PROCEDURE Receiver(): D.Object;
      VAR
        receiver: D.Object;
      BEGIN
        mode := D.objTBProc;
        S.GetSym;
        IF (S.sym = S.var) THEN
          rmode := D.objVarPar;
          S.GetSym
        ELSE
          rmode := D.objVar
        END;
        IF (S.sym = S.ident) THEN
          receiver := Sym.NewObject (S.str^, rmode, S.currSymPos);
          S.GetSym
        ELSE
          receiver := Sym.NewObject (S.undefStr, rmode, S.currSymPos);
          E.Err (S.currSymPos, 100)    (* identifier expected *)
        END;
        receiver. flags := receiver. flags + {D.objIsParameter, D.objIsReceiver};
        receiver. moduleId := Sym.currScope. moduleId;
        receiver. level := Sym.currScope. level+1;
        S.CheckSym (S.colon);
        receiver. type := Type ({typeIsParameter, typeIsReceiver}, noExport);
        record := receiver. type;
        IF (record. form = D.strPointer) THEN
          record := record. base;
          IF (rmode # D.objVar) THEN
            E.Err (receiver. pos, 214)  
            (* pointer receiver has to be value parameter *)
          END
        ELSIF (record. form = D.strRecord) & (rmode # D.objVarPar) THEN
          E.Err (receiver. pos, 215)  
          (* record receiver has to be value *)
        END;
        
        IF (record. form # D.strRecord) THEN
          E.Err (receiver. pos, 216);  (* illegal receiver type *)
          record := D.struct[D.strUndef]
        ELSIF (record. obj # NIL) &
              (Sym.ImportedObject (Sym. mod, record. obj) OR
               (record. obj. level # Sym.globalLevel)) THEN
          E.Err (receiver. pos, 217);  (* has to be level 0 *)
          record := D.struct[D.strUndef]
        END;
        S.CheckSym (S.rParen);
        IF (Sym.currScope # Sym.mod) THEN
          E.Err (S.currSymPos, 218)  
          (* type-bound procedure has to be defined on top level *)
        END;
        RETURN receiver
      END Receiver;
    
    PROCEDURE CompareParamNames (recForw, recNew: D.Object; fpForw, fpNew: D.Struct);
    (* Compares parameter (and receiver) names of the actual definition with 
       the forward declaration.  Any mismatch is marked with a warning.  *)
      VAR
        objForw, objNew: D.Object;
      BEGIN
        IF (recForw # NIL) & (recForw. name^ # recNew. name^) THEN
          E.Err (recNew. pos, -403)
          (* warning: parameter name differs from forward declaration *)
        END;
        objForw := fpForw. decl; objNew := fpNew. decl;
        WHILE (objForw # NIL) DO
          IF (objForw. name^ # objNew. name^) THEN
            E.Err (objNew. pos, -403)
            (* warning: parameter name differs from forward declaration *)
          END;
          objForw := objForw. rightObj; objNew := objNew. rightObj
        END
      END CompareParamNames;
    
    PROCEDURE CheckRecordEntries (record: D.Struct; proc: D.Object);
    (* Check that the newly into `record' inserted type-bound procedure `proc'
       doesn't collide with the names of record fields in one of `record's 
       extensions and that no type-bound procedure of the same name was defined
       in one of the extensions.  *)
      VAR
        struct: Sym.StructList;
        base: D.Object;
      BEGIN
        struct := Sym.typeConstrList;
        WHILE (struct # NIL) DO
          IF (struct. type. form = D.strRecord) & 
             Sym.ExtensionOf (struct. type, record) THEN
            base := Sym.FindField (struct. type, proc. name^);
            IF (base # proc) THEN
              IF (base. mode = D.objField) THEN
                E.ErrIns (proc.pos, 225, base. localTo(D.Struct). obj. name^)
                (* field of this name already declared in extension *)
              ELSE
                E.ErrIns (proc.pos, 226, base. localTo(D.Struct). obj. name^)
                (* tb procedure has been declared in extension first *)
              END
            END
          END;
          struct := struct. next
        END
      END CheckRecordEntries;
    
    PROCEDURE FixupTBCalls (record: D.Struct; proc, base: D.Object);
      VAR
        use, next, prev, opnd: D.Opnd;
        static: D.Struct;
        call: D.Instruction;
      
      PROCEDURE ReplaceLocations (opnd: D.Opnd);
      (* Replaces locations of all arguments for formal parameters.  First 
         determines the new locations for _all_ arguments, then replaces them
         all at once.  *)
        VAR
          obj, new: D.Object;
        BEGIN
          obj := opnd. GetFormalParam();
          IF (obj # NIL) THEN
            IF (obj. name^ = proc. data(D.Object). name^) THEN
              new := proc. data(D.Object)
            ELSE
              new := proc. type. decl;
              WHILE (obj. name^ # new. name^) DO
                new := new. rightObj
              END
            END;
            IF (opnd. nextOpnd # NIL) THEN
              ReplaceLocations (opnd. nextOpnd)
            END;
            opnd. location := D.CreateSymLocation (new,
                                         opnd. location(D.SymLocation). attrib)
          END
        END ReplaceLocations;
      
      BEGIN
        (* scan all uses of `base' in instructions with opcode `tbProcAdr' *)
        use := base. useList;
        WHILE (use # NIL) DO
          next := use. nextUse;
          IF (use. instr. opcode = Opc.tbProcAdr) THEN
            (* extract static record type *)
            prev := use. instr. opndList;
            WHILE (prev. nextOpnd # use) DO
              prev := prev. nextOpnd
            END;
            static := prev. arg(D.Struct);
            IF Sym.ExtensionOf (static, record) THEN
              call := use. instr. useList. instr;
              (* replace locations of all arguments to refer to the new proc *)
              ReplaceLocations (call. NthOperand (3));
              (* replace `base' with the more recent redefinition `proc' *)
              use. ReplaceOperand (proc);
              (* replace second operand of call with the corrected formal
                 parameters, the third with the new procedure *)
              opnd := call. NthOperand (1);
              opnd. ReplaceOperand (proc. type);
              opnd := call. NthOperand (2);
              opnd. ReplaceOperand (proc)
            END
          END;
          use := next
        END
      END FixupTBCalls;
    
    PROCEDURE ReplaceLocations (proc: D.Object; oldProc: D.ObjectDesc);
    (* For every call of procedure `proc' replace all references in symbolic
       locations to formal parameters in `oldFPar' with the correct ones in
       `proc. type'.  This removes all references to the formal parameters of
       a forward declared procedure from the GSA code.  *)
      VAR
        oldPar, currPar: D.Object;
        use, opnd: D.Opnd;
        var: D.Addressable;
      BEGIN
        (* prepare old parameter objects *)
        oldPar := oldProc. type. decl;
        currPar := proc. type. decl;
        WHILE (oldPar # NIL) DO
          oldPar. data := currPar;
          oldPar. name := NIL;
          oldPar := oldPar. rightObj;
          currPar := currPar. rightObj
        END;
        IF (proc. data # NIL) THEN  (* receiver *)
          oldProc. data(D.Object). data := proc. data;
          oldProc. data(D.Object). name := NIL
        END;
        
        use := proc. useList;
        WHILE (use # NIL) DO
          IF (use. instr. opcode = Opc.call) &
             (use. instr. NthOperand (2) = use) THEN
            (* replace formal parameters *)
            opnd := use. instr. NthOperand (1);
            opnd. ReplaceOperand (proc. type);
            (* there is no need to replace the procedure object, since the
               object of the forward declaration is recycled *)
            
            (* replace `var' attributes of locations *)
            opnd := use. instr. NthOperand (3);
            WHILE (opnd # NIL) DO
              var := opnd. location(D.SymLocation). var;
              IF (var IS D.Object) & (var(D.Object). name = NIL) THEN
                opnd. location := D.CreateSymLocation (
                                     var(D.Object). data(D.Object),
                                     opnd. location(D.SymLocation). attrib)
              END;
              opnd := opnd. nextOpnd
            END
          END;
          use := use. nextUse
        END
      END ReplaceLocations;
    
    BEGIN  (* pre: S.sym = S.procedure *)
      S.GetSym;
      mode := D.objProc;
      forward := (S.sym = S.arrow);
      IF forward THEN
        S.GetSym
      END;
      
      IF (S.sym = S.lParen) THEN  (* type bound procedure: parse receiver *)
        receiver := Receiver()
      ELSE
        receiver := NIL; record := NIL; rmode := D.objVar
      END;
      
      prevDecl := NIL;
      base := NIL;
      SkipModifiers (modifierScan, modifiers);
      IF (S.sym = S.ident) THEN
        (* first examine if a forward declaration of this name exists *)
        IF (receiver # NIL) THEN
          IF (record. form = D.strRecord) THEN
            prevDecl := Sym.FindDecl (record, S.str^)
          END
        ELSE
          prevDecl := Sym.FindDecl (Sym.currScope, S.str^)
        END;
        (* ignore any previous declaration if it isn't of the right form *)
        IF (prevDecl = NIL) OR (prevDecl. mode # mode) OR
           ~(D.objIsForwardDecl IN prevDecl. flags) THEN
          prevDecl := NIL
        END;
        
        (* here holds: `prevDecl # NIL' iff a forward declaration named 
          `S.str^' of the right mode exists *)
        IF (prevDecl # NIL) THEN
          IF forward THEN
            E.Err (S.currSymPos, 219)    (* multiple forward declaration *)
          END;
          prevContent := prevDecl^
        END;
        proc := IdentDef (prevDecl, mode, exp-1)
        (* here holds: `prevDecl # NIL' implies `proc = prevDecl' *)
      ELSE
        proc := Sym.NewObject (S.undefStr, mode, S.currSymPos);
        E.Err (S.currSymPos, 100);     (* identifier expected *)
        modifiers := FALSE;
        S.GetSym
      END;
      
      proc. data := receiver;
      (* set forward flag *)
      IF forward THEN
        INCL (proc. flags, D.objIsForwardDecl)
      ELSIF (D.objIsForwardDecl IN proc. flags) THEN
        EXCL (proc. flags, D.objIsForwardDecl);
        INCL (proc. flags, D.objWasForwardDecl)
      END;
      
      (* parse procedure modifiers; problem: these modifiers appear before
         the name, but have to be parsed afterwards;  so move the scanning
         position backwards, parse them, and change the position back again*)
      IF modifiers THEN
        (* only do save/restore if modifiers exist *)
        S.SaveScanPos (modifierEnd);
        S.RestoreScanPos (modifierScan);
        SystemFlags.ObjectModifiers (proc, TRUE);
        S.RestoreScanPos (modifierEnd)
      ELSE  
        (* we need to pass control to the back-end, because it may change some
           flags associated with the procedure; we don't want to do the save/
           restore thingy, but we can't have any type flags at this point 
           mistaken for object related flags; making sure that S.sym#S.lBrak 
           should suffice *)
        oldSym := S.sym;
        S.SetSym (S.ident);
        SystemFlags.ObjectModifiers (proc, TRUE);
        S.SetSym (oldSym)
      END;
      
      FormalPars (proc. type);
      Sym.MakeFormalParsLocal (proc);
      IF (prevDecl # NIL) THEN  (* this resolves a forward declaration *)
        (* make sure that forward declaration and definition match *)
        IF ~Sym.ParamsMatch (prevContent. type, proc. type, FALSE) THEN
          E.Err (proc. pos, 220)  
          (* parameter list doesn't match forward declaration *)
        ELSIF (receiver # NIL) & 
              (prevContent. data(D.Object). mode # rmode) THEN
          E.Err (receiver. pos, 221)  
          (* receiver doesn't match forward declaration *)
        ELSIF (prevContent. data # NIL) THEN
          CompareParamNames (prevContent. data(D.Object), receiver, 
                             prevContent. type, proc. type)
        ELSE
          CompareParamNames (NIL, NIL, prevContent. type, proc. type)
        END;
        
        IF E.noerr THEN
          ReplaceLocations (proc, prevContent)
        END
      END;
      
      IF (receiver # NIL) & (record. form = D.strRecord) THEN  (* tb proc *)
        (* if type-bound procedure: locate base definition and make sure that
           the receivers and formal parameters match *)
        base := Sym.BaseDefinition (receiver, proc. name^);
        IF (base # NIL) THEN
          IF ~Sym.ParamsMatch (proc. type, base. type, 
                               ~StdPragmas.conformantMode. true) THEN
            E.Err (proc. pos, 223)  
            (* parameter list doesn't match inherited declaration *)
          ELSIF (base. data(D.Object). mode # rmode) THEN
            E.Err (receiver. pos, 224)  
            (* receiver doesn't match inherited declaration *)
          ELSIF (D.objIsExported IN base. flags) &
                ~(D.objIsExported IN proc. flags) THEN
            E.Err (proc. pos, 202)
            (* has to be exported like base procedure *)
          END
        END;
        (* add procedure to the record's field list *)
        IF (prevDecl = NIL) THEN
          Sym.InsertField (record, proc);
          (* make sure that no type-bound procedures of this name have already
             been declared in extensions of the receiver *)
          CheckRecordEntries (record, proc);
          (* fixup any calls that had `proc's record type as receiver and were 
             directed to the base declaration *)
          IF (base # NIL) THEN
            FixupTBCalls (record, proc, base)
          END
        END
      ELSIF (prevDecl = NIL) THEN  (* insert normal procedure *)
        Sym.Insert (proc)
      END;
      INCL (Sym.currScope. flags, D.objContainsProc);
      
      SystemFlags.ObjectModifiers (proc, FALSE);
      IF ~(forward OR ~(D.objHasBody IN proc. flags)) THEN
        S.CheckSym (S.semicolon);
        Sym.OpenScope (proc, Sym.currScope. moduleId, Sym.currScope. level+1);
        (* put parameters into the procedure's symbol table *)
        Sym.InsertParams (proc); 
        DeclSeq (noExport);
        greg := Attr.InitGreg (Attr.CreateGreg (proc), exitInfo);
        IF (S.sym = S.begin) THEN
          IF (D.objAbstractTBProc IN proc. flags) THEN
            E.Err (S.currSymPos, 453)  (* no BEGIN allowed in abstract proc *)
          END;
          
          IF StdPragmas.stackCheck. true THEN
            INCL (greg. enter. flags, D.instrStackCheck);
            Attr.ContainsRuntimeCheck (greg)
          END;
          
          Statm.InitVariables (greg, proc. localDecl, S.currSymPos);
          S.GetSym;
          Statm.StatementSeq (greg, exitInfo);
          Attr.CleanupGreg (greg)
        END;
        Attr.GuardExit (greg, exitInfo);
        FinishRegion (greg, exitInfo);
        Attr.UnguardExit (greg, exitInfo);
        proc. greg := greg;
        S.CheckSym (S.end);
        IF (S.sym # S.ident) OR (S.str^ # proc. name^) THEN
          E.ErrIns (S.currSymPos, 198, proc. name^) 
          (* procedure identifier expected *)
        END;
        S.GetSym;
        Sym.CloseScope (E.noerr)
      ELSE
        greg := NIL
      END;
      IF E.noerr THEN
        IF forward THEN
          (* notify back-end of the forward declaration *)
          CodeGen.ForwardProcedure (moduleData, proc)
        ELSE
          (* pass procedure's greg to back-end; if it's an external declaration
             `greg' will be NIL *)
          CodeGen.FinishProcedure (moduleData, proc, greg)
        END
      END
    END ProcDecl;

  PROCEDURE FixForwardPointers (base: D.Struct);
  (* Locates all pointer types that refer to `base' before the type is
     actually declared and completes their definition.  *)
    
    PROCEDURE TraverseTree (obj: D.Object);
      PROCEDURE FixType (t: D.Struct);
      (* pre: `t' is an unnamed type or part of a type declaration placed in 
              the current scope `Sym.currScope'  *)
        BEGIN
          CASE t. form OF
          | D.strPointer:
            IF (t. base = base) THEN
              SystemFlags.StructModifiers (t, FALSE)
            END
          | D.strProc, D.strRecord:
            TraverseTree (t. decl)  (* actually this is a list *)
          | D.strArray, D.strOpenArray:
            IF (t. base. obj = NIL) THEN
              FixType (t. base)
            END
          ELSE  (* ignore *)
          END
        END FixType;
      
      BEGIN
        IF (obj # NIL) THEN
          TraverseTree (obj. leftObj);
          IF (obj. mode = D.objType) & (obj. type. obj = obj) OR
             (obj. mode IN {D.objVar, D.objVarPar, D.objField}) & 
               (obj. type. obj = NIL) THEN
            (* only consider unnamed types and the rhs of a type declaration *)
            FixType (obj. type)
          END;
          TraverseTree (obj. rightObj)
        END
      END TraverseTree;
    
    BEGIN
      TraverseTree (Sym.currScope. localDecl)
    END FixForwardPointers;
  
  PROCEDURE ReplaceTypeRef (old, new: D.Struct);
  (* Replace all references to type `old' with `new'.
     pre: `old.type' is a forward placeholder *)
     
    PROCEDURE TraverseTree (obj: D.Object);
      PROCEDURE FixType (VAR t: D.Struct);
      (* pre: `t' is an unnamed type or part of a type declaration placed in 
              the current scope `Sym.currScope'  *)
        BEGIN
          IF (t = old) THEN
            t := new
          END;
          CASE t. form OF
          | D.strPointer:
            IF (t. base. obj = NIL) THEN
              FixType (t. base)
            ELSIF (t. base = old) THEN
              t. base := new
            END
          | D.strProc, D.strRecord:
            TraverseTree (t. decl)  (* actually this is a list *)
          | D.strArray, D.strOpenArray:
            IF (t. base. obj = NIL) THEN
              FixType (t. base)
            END
          ELSE  (* ignore *)
          END
        END FixType;
      
      BEGIN
        IF (obj # NIL) THEN
          TraverseTree (obj. leftObj);
          IF (obj. mode = D.objType) & (obj. type. obj = obj) OR
             (obj. mode IN {D.objVar, D.objVarPar, D.objField}) & 
               (obj. type. obj = NIL) THEN
            (* only consider unnamed types and the rhs of a type declaration *)
            FixType (obj. type)
          END;
          TraverseTree (obj. rightObj)
        END
      END TraverseTree;
    
    BEGIN
      TraverseTree (Sym.currScope. localDecl)
    END ReplaceTypeRef;
  
  BEGIN
    LOOP
      IF (S.sym = S.const) THEN  (* constant declaration *)
        S.GetSym;
        WHILE (S.sym = S.ident) DO
          obj := IdentDef (NIL, D.objConst, exp-1);
          S.CheckSym (S.eql);
          obj. data := Expr.ConstExpr (D.grpAnyType);
          obj. type := obj. data(D.Const). type;
          IF (D.objIsExported IN obj. flags) THEN
            obj. data(D.Const). preserve := TRUE
          END;
          Sym.Insert (obj);
          S.CheckSym (S.semicolon)
        END
        
      ELSIF (S.sym = S.type) THEN  (* type declaration *)
        S.GetSym;
        WHILE (S.sym = S.ident) DO
          obj := IdentDef (NIL, D.objType, exp-1);
          S.CheckSym (S.eql);
          obj. type := Type ({}, exp);
          (* does a forward declared type of this name exist?  problem: the
             type we just parsed may have introduced a forward declaration, so
             we can't deal with this case when we create `obj' in the first 
             place *)
          prev := Sym.FindDecl (Sym.currScope, obj. name^);
          IF (prev = NIL) OR (prev. mode # D.objType) OR
             ~(D.objIsForwardDecl IN prev. flags) THEN
            prev := NIL
          END;
          
          IF (prev = NIL) THEN
            IF (obj. type. obj = NIL) THEN  (* set name if type is unnamed *)
              obj. type. obj := obj
            END;
            Sym.Insert (obj)
          
          ELSE
            (* resolving forward type; here holds: `obj' holds the type 
               declaration, `prev' the old forward declaration that is 
               resolved by `obj' *)
            type := obj. type;
            IF ~Sym.TypeInGroup (type, D.grpArray) & 
               (type. form # D.strRecord) & (type. form # D.strUndef) THEN
              E.Err (obj. pos, 267)
              (* illegal definition for a previously used pointer base type *)
            END;
            
            (* don't insert `obj' into the scope, but rather move the relevant
               attributes of `obj' into `prev'; copy the new type into the old 
               location, adjust `localTo' field of record fields to refer to 
               `prev.type' instead of `type'; change entry in 
               `Sym.typeConstrList' to refer to `prev.type' *)
            prev. beInfo := obj. beInfo;
            IF (type. obj # NIL) THEN
              (* forward declaration is resolved by means of an alias
                 declaration; because such a declaration does not introduce
                 a new instance of `Data.Struct', we cannot copy anything into
                 the struct `prev.type' without breaking the primary invariant
                 of the type system: one data type, one struct; the fix: treat
                 the alias like a normal declaration, but replace all uses
                 of `prev. type' with `obj. type' *)
              ReplaceTypeRef (prev. type, obj. type)
            ELSE
              prev. type^ := type^;
              prev. type. obj := prev;
              prev. type. currValue := prev. type
            END;
            prev. mode := obj. mode;
            prev. flags := obj. flags+{D.objWasForwardDecl, D.objIsUsed};
            prev. pos := obj. pos;
            IF (type. form = D.strRecord) THEN
              first := type. decl;
              WHILE (first # NIL) DO
                IF (first. localTo = type) THEN
                  first. localTo := prev. type
                END;
                first := first. rightObj
              END
            END;
            IF Sym.TypeInGroup (type, D.grpArray) OR 
               (type. form = D.strRecord) THEN
              structList := Sym.typeConstrList;
              WHILE (structList. type # type) DO
                structList := structList. next
              END;
              structList. type := prev. type
            END;
            obj := prev
          END;
          
          IF (prev = NIL) THEN
            FixForwardPointers (type)
          END;
          IF (D.objIsExported IN obj. flags) THEN
            INCL (obj. type. flags, D.structIsExported)
          END;
          S.CheckSym (S.semicolon)
        END
        
      ELSIF (S.sym = S.var) THEN  (* variable declaration *)
        S.GetSym;
        WHILE (S.sym = S.ident) DO
          IdentList (first, last, D.objVar, exp);  (* read ident list *)
          S.CheckSym (S.colon);
          (* and the variable's type:  *)
          last. type := Type ({typeNotOpenArray, typeNotAbstract}, exp);
          (* set type for all variables in the identifier list and insert the 
             variable objects into the current scope *)
          obj := first;
          WHILE (obj # NIL) DO
            first := obj. rightObj;
            obj. type := last. type;
            Sym.Insert (obj);
            SystemFlags.ObjectModifiers (obj, FALSE);
            obj := first
          END;
          S.CheckSym (S.semicolon)
        END
      ELSE
        EXIT
      END
    END;
    
    (* parse list of procedure declarations *)
    WHILE (S.sym = S.procedure) DO
      ProcDecl;
      S.CheckSym (S.semicolon)
    END
  END DeclSeq;


PROCEDURE Module* (progData: CodeGen.Program): CodeGen.Module;
(* Parses the module and builds GSA code.  The generated intermediate code is 
   passed to the back-end by calling `CodeGen.FinishProcedure' and `CodeGen.
   FinishModule'.  Unless an early error occured, the result is an auxiliary
   data structure (managed by the the back-end) to collect the module's
   data, otherwise the result is NIL.  The argument `progData' is passed
   directly to `CodeGen.CreateModule' and can be NIL.  *)
  VAR
    name: Parameter.Filename;
    greg: D.GlobalRegion;
    exitInfo: Attr.ExitInfo;
    result: CodeGen.Module;
    
  PROCEDURE CompareWithFile (moduleName: ARRAY OF CHAR;
                             VAR fileName: ARRAY OF CHAR): BOOLEAN;
    VAR 
      d, f, m: Parameter.Filename;
      pos: INTEGER;
    BEGIN
      Filenames.GetPath (fileName, d, f);
      Filenames.GetFile (f, f);
      pos := Strings.Length (moduleName);
      LOOP
        (* extract last part of module name *)
        WHILE (pos # 0) & (moduleName[pos-1] # S.moduleSeparator) DO
          DEC (pos)
        END;
        Strings.Extract (moduleName, pos, MAX (INTEGER), m);
        
        (* compare last part of file name with last part of module name *)
        IF (m # f) THEN
          Strings.Delete (fileName, 0, Strings.Length (d));
          RETURN FALSE
        ELSIF (pos = 0) THEN
          RETURN TRUE
        END;
        
        (* strip last part from names *)
        DEC (pos);
        moduleName[pos] := 0X;
        IF (d = "") THEN
          RETURN FALSE
        ELSE
          d[Strings.Length(d)-1] := 0X;  (* remove trailing dir separator *)
          Filenames.GetPath (d, d, f)
        END
      END
    END CompareWithFile;
  
  PROCEDURE ImportList;
  (* Parses list of module imports, imports their symbole files, and inserts 
     their respective alias name into the symbol table. *)
    VAR
      pos: LONGINT;
      import: D.Object;
      modId, alias: ARRAY 4096 OF CHAR;
      found: BOOLEAN;
      i: INTEGER;
    BEGIN  (* pre: S.sym = import *)
      S.moduleIdent := TRUE;
      S.GetSym;
      LOOP
        IF (S.sym = S.ident) THEN
          COPY (S.str^, modId);
          COPY (S.str^, alias);
          
          (* if the name contains multiple parts, remove all but the very 
             last name component *)
          Strings.FindPrev (S.moduleSeparator, alias, MAX (INTEGER), found, i);
          IF found THEN
            Strings.Delete (alias, 0, i+1)
          END;
          
          pos := S.currSymPos;
          S.GetSym;
          IF (S.sym = S.becomes) THEN
            Strings.FindPrev(S.moduleSeparator, modId, MAX(INTEGER), found, i);
            IF found THEN
              E.Err (pos, 100)           (* identifier expected *)
            END;
            
            S.GetSym;
            IF (S.sym = S.ident) THEN
              COPY (S.str^, modId);
              pos := S.currSymPos;
              S.GetSym
            ELSE
              E.Err (S.currSymPos, 100)  (* identifier expected *)
            END
          END;
          IF (modId = Sym.mod. name^) THEN
            E.Err (pos, 306)             (* module can't import itself *)
          ELSE
            import := SymbolFile.Read (modId, pos);
            IF (import # NIL) THEN       (* set alias name and insert module *)
              NEW (import. name, Strings.Length (alias)+1);
              COPY (alias, import. name^);
              Sym.Insert (import)
            END
          END
        ELSE
          E.Err (S.currSymPos, 100)  (* identifier expected *)
        END;
        IF (S.sym # S.comma) THEN
          EXIT
        END;
        S.GetSym
      END;
      S.moduleIdent := FALSE;
      S.CheckSym (S.semicolon)
    END ImportList;

  BEGIN
    greg := NIL;
    moduleData := NIL;
    S.moduleIdent := TRUE;
    S.CheckSym (S.module);
    S.moduleIdent := FALSE;
    IF E.noerr THEN
      IF (S.sym = S.ident) THEN
        (* compare module name with the source file's name *)
        COPY (E.sourceFile^, name);
        IF ~CompareWithFile (S.str^, name) THEN 
          E.ErrIns (S.currSymPos, -400, name)
          (* warning: file name doesn't match module name *)
        END;
        
        (* if the module's symbol file is loaded, get rid of it and of all 
           symbol tables of modules that depend on it *)
        SymbolFile.RemoveImportedModule (S.str^);
        (* create root of symbol table; store source file in data.string *)
        Sym.mod := Sym.NewModule (S.str^, S.currSymPos);
        Sym.mod. data(D.Const). string := E.sourceFile;
        Sym.OpenScope (Sym.mod, Sym.currentModuleId, Sym.globalLevel);
        S.GetSym;
        SystemFlags.ObjectModifiers (Sym.mod, TRUE);
        S.CheckSym (S.semicolon);
        
        (* create information block that will collect this module's data *)
        moduleData := CodeGen.CreateModule (progData, Sym.mod);
        
        (* parse import list *)
        IF (S.sym = S.import) THEN
          ImportList
        END;
        
        IF E.noerr THEN  
          (* useless to proceed here if we already encountered an error in the
             module header or import list; otherwise continue to parse 
             declarations *)
          
          (* enable underscore if the module allows it instead of a letter *)
          S.allowUnderscore := (D.objAllowsUnderscore IN Sym.mod. flags);
          
          DeclSeq (anyExport);
          Sym.BalanceTree (Sym.mod);
    	  (* parse the module's initialization code (if it exists) *)
          IF (D.objHasBody IN Sym.mod. flags) THEN
            greg := Attr.InitGreg (Attr.CreateGreg (Sym.mod), exitInfo);
            Statm.InitVariables (greg, Sym.mod. localDecl, S.currSymPos);
            IF (S.sym = S.begin) THEN
              IF StdPragmas.stackCheck. true THEN
                INCL (greg. enter. flags, D.instrStackCheck);
                Attr.ContainsRuntimeCheck (greg)
              END;
              
              S.GetSym;
              Statm.StatementSeq (greg, exitInfo);
              Attr.CleanupGreg (greg);
              Attr.GuardExit (greg, exitInfo)
            END;
            FinishRegion (greg, exitInfo);
            Sym.mod. greg := greg
          END;
          S.moduleIdent := TRUE;
          S.CheckSym (S.end);
          S.moduleIdent := FALSE;
          IF (S.sym # S.ident) OR (S.str^ # Sym.mod. name^) THEN
            E.ErrIns (S.currSymPos, 198, Sym.mod. name^) 
            (* module identifier expected *)
          END;
          S.GetSym;
          S.CheckSym (S.period);
          S.CheckPragmas
        END;
        Sym.CloseScope (E.noerr);
        SystemFlags.ObjectModifiers (Sym.mod, FALSE)
      ELSE
        E.Err (S.currSymPos, 100)  (* identifier expected *)
      END
    END;
    
    IF E.noerr & (moduleData # NIL) THEN
      CodeGen.FinishModule (moduleData, greg, Sym.typeConstrList)
    END;
    
    result := moduleData;
    (* clear the front-end's global variables *)
    E.sourceFile := NIL;                 (* invalidate calls to E.ErrXXX *)
    Sym.mod := NIL;
    Sym.typeConstrList := NIL;
    moduleData := NIL;
    RETURN result
  END Module;

BEGIN
  removeDeadCode := TRUE
END ParseDecl.
