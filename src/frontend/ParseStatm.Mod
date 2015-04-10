(* 	$Id: ParseStatm.Mod,v 1.138 2000/12/27 16:32:32 ooc-devel Exp $	 *)
MODULE ParseStatm;
(*  Parses Oberon-2 statements and translates them to GSA.
    Copyright (C) 1995-2000  Michael van Acken

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
  IntStr, 
  Config, E := Error, S := Scanner, D := Data, StdTypes, StdPragmas, 
  Sym := SymbolTable, Opc := Opcode, Expr := ParseExpr, Attr := Attributes;


VAR
  setAssignHints*: BOOLEAN;
  (* when set the front-end tries to mark assignments in the GSA code by 
     setting the assigned instruction's location field, otherwise it'll stay 
     NIL; only useful when writing the GSA code to stdout, make sure to disable
     this when the GSA code is run through a storage or register allocator  *)


PROCEDURE AssignmentCompatible (region: D.Region; varType: D.Struct; VAR expr: Attr.Item);
(* Writes an error if `expr' isn't assignment compatible to `varType'.
   side: If `varType' and `expr' are numeric and assignment compatible, `expr'
     is converted to the type `varType'.  If a character constant in `expr' is
     assigned to a string, it's converted into a string constant of length 1.*)
  VAR
    comp: BOOLEAN;
    tv, te: SHORTINT;
  
  PROCEDURE CArrayAssignCompatible (tv, te: D.Struct): BOOLEAN;
    BEGIN
      IF Sym.TypeInGroup (tv, D.grpArray) THEN
        IF Sym.TypeInGroup (te, D.grpArray) THEN
          RETURN CArrayAssignCompatible (tv. base, te. base)
        ELSE
          RETURN Sym.TypeInGroup (tv. base, D.grpChar) &
                 Expr.StringConvertible (expr, tv)
        END
      ELSE
        RETURN (tv = te)
      END
    END CArrayAssignCompatible;
  
  BEGIN
    Expr.CheckValue (expr);
    
    tv := varType. form; te := expr. type. form;
    IF (tv = D.strUndef) OR (te = D.strUndef) THEN
      comp := TRUE                       (* var or expr is erroneous *)
      
    ELSIF Sym.Includes (varType, expr. type, D.grpNumeric) OR
          Sym.Includes (varType, expr. type, D.grpChar) THEN
      comp := TRUE;
      Expr.TypeConversion (region, expr, tv, FALSE, expr. pos)
      
    ELSIF (tv = D.grpAnyString) THEN
      (* first parameter of COPY: accept any strings and also any character 
         constants; the latter are converted into string constants *)
      comp := Sym.TypeInGroup (expr. type, D.grpAnyString) OR
              Expr.StringConvertible (expr, D.struct[D.strStringConst8]) OR
              Expr.StringConvertible (expr, D.struct[D.strStringConst16])
              
    ELSIF Sym.SameType (varType, expr. type) OR
    
          Sym.ExtensionOf (expr. type, varType) OR
          
          Sym.TypeInGroup (varType, D.grpNilCompat) & (te = D.strNil) OR
               
          (tv = D.strProc) & (expr. obj # NIL) & 
            (expr. obj. mode = D.objProc) &
            Sym.GlobalDecl (expr. obj) &
            ~(D.objIsSpecialCodeProc IN expr. obj. flags) &
            Sym.ParamsMatch (varType, expr. type, FALSE) THEN
      comp := TRUE
    
    ELSIF (tv = D.strArray) & Sym.TypeInGroup (varType. base, D.grpChar) THEN
      (* assigning character or string constant to character array *)
      comp := (expr. const # NIL) &
      
              ((Sym.TypeInGroup (expr. type, D.grpStringConst) &
                (varType. len > expr. const. int)) OR
               (Sym.TypeInGroup (expr. type, D.grpChar) &
                 ((expr. const. int # 0) & (varType. len > 1) OR
                  (expr. const. int = 0) & (varType. len > 0)))) &
                  
              Expr.StringConvertible (expr, varType)
      
    ELSIF (tv = D.strByte) & (te IN {D.strChar8, D.strShortInt, D.strSet8}) OR
          (tv = D.strPtr) & (te = D.strPointer) THEN
      comp := TRUE
      
    ELSIF Sym.TypeInGroup (expr. type, varType. form) THEN
      comp := TRUE
      
    ELSIF (D.structCArrayAssign IN varType. flags) &
          CArrayAssignCompatible (varType. base, expr. type) THEN
      comp := TRUE;
      Attr.CreateItem (expr, Attr.Adr (region, expr), expr. pos)
    
    ELSIF ((tv = D.grpShort) OR (tv = D.grpLong)) &
          Sym.TypeInGroup (expr. type, D.grpInteger) &
          (expr. const # NIL) THEN
       (* LONG or SHORT on an constant expression of integer type is
          always allowed; it is a noop, changing neither the value, nor
          the type, of the integer constant *)
      comp := TRUE
      
    ELSE
      comp := FALSE
    END;
    IF ~comp THEN
      Sym.ErrT1 (expr. pos, 239, varType)
      (* not assignment compatible to type *)
    END
  END AssignmentCompatible;

PROCEDURE WritableVariable (VAR x: Attr.Item);
(* Writes an error if `x' isn't a variable that can be written to.  *)
  BEGIN
    Expr.CheckValue (x);
    IF (x. const # NIL) OR ~x. designator THEN
      E.Err (x. pos, 244)                (* not a variable designator *)
    ELSIF (x. readOnlyPos # D.undefPos) THEN
      IF (x. readOnlyPos > 0) THEN
        E.Err (x. readOnlyPos, 245)      (* this is imported read-only *)
      ELSE
        E.Err (-x. readOnlyPos, 269)
        (* cannot modifiy value parameter that has no local copy *)
      END
    END
  END WritableVariable;


PROCEDURE AddToExit (region: D.Region; var: D.Addressable);
(* Adds `var' as operand to exit instruction of region.  *)
  VAR
    exit: D.Instruction;
  BEGIN
    exit := region. ExitInstr();
    IF (exit. GetOperand (var, D.symLocObject) = NIL) THEN
      exit. Operand (var);
      exit. SetOpndSymLoc (var)
    END
  END AddToExit;

PROCEDURE CorrectCondGate (region: D.Region; value: D.Usable): D.Usable;
(* If `value' is a gate of a "merge-cond:" instruction that combines the true
   and false path of an OR or &, then replace `value' by the appropriate
   gate operand, otherwise return `value'.  *)
  VAR
    gate: D.Gate;
  BEGIN
    IF (value IS D.Gate) THEN
      gate := value(D.Gate);
      IF (gate. region. opcode = Opc.mergeCond) &
         (gate. region. opndList. arg = region) THEN
        RETURN gate. opndList. nextOpnd. arg
      ELSIF (gate. region. opcode = Opc.mergeCond) &
            (gate. region. opndList. nextOpnd. arg = region) THEN
        RETURN gate. opndList. nextOpnd. nextOpnd. arg
      END
    END;
    RETURN value
  END CorrectCondGate;

PROCEDURE AssignToVar (region: D.Region; dest: D.Object; VAR x: Attr.Item);
(* Assigns value of `x' to `dest', ie, sets `value' as `dest's current value; 
   gates are created, or updated, if necessary.  The values of the operands of
   newly created gates are taken from `dest. currValue', the operand 
   corresponding to `region' is then replaced by the value of `x'.  *)
  VAR 
    opnd: D.Opnd;
    gate: D.Gate;
    merge: D.Merge;
    instr, exit: D.Instruction;
    type: D.Struct;
    y: Attr.Item;
    source, otherValue: D.Usable;
    combined: INTEGER;
    greg: D.GlobalRegion;
    
  PROCEDURE FindGate (merge: D.Region; var: D.Addressable): D.Gate;
  (* Finds gate in `merge' regions that merges the different values of the
     variable or structure `var'.  Result is NIL if no such gate exists yet. *)
    VAR
      instr: D.Instruction;
    BEGIN
      instr := merge. instrList;
      WHILE (instr # NIL) & 
            (~(instr IS D.Gate) OR (instr(D.Gate). var # var)) DO
        instr := instr. nextInstr
      END;
      (* here holds: (instr = NIL) OR 
                     ((instr IS D.Gate) & (instr. var = var)) *)
      IF (instr = NIL) THEN
        RETURN NIL
      ELSE
        RETURN instr(D.Gate)
      END
    END FindGate;
  
  PROCEDURE ReplaceGateOperand (gate: D.Gate; region: D.Region; value: D.Usable);
  (* Replaces the operand corresponding to `region' in `gate' by `value'.  
     Note that there has to exist such an operand beforehand.  *)
    VAR
      merge: D.Merge;
      opndMerge, opndGate: D.Opnd;
    BEGIN
      merge := gate. opndList. arg(D.Merge);
      opndGate := gate. opndList. nextOpnd;
      IF (merge. opcode = Opc.mergeLoop) THEN
        (* the merge that this gate is referencing is a loop merge and 
           therefore incomplete; replace 3rd operand *)
        opndGate. nextOpnd. ReplaceOperand (value)
      ELSE
        opndMerge := merge. opndList;
        WHILE ~Expr.Dominates (opndMerge. arg(D.Region), region) DO
          opndMerge := opndMerge. nextOpnd;
          opndGate := opndGate. nextOpnd
        END;
        opndGate. ReplaceOperand (value)
      END
    END ReplaceGateOperand;
  
  PROCEDURE FixupLoopGate (lmerge: D.Region; gate: D.Gate);
  (* Replaces all uses of the variable (or rather, its value) associated with
     `gate' in the region `lmerge' and all regions that are dominated by it 
     (i.e. that are nested in it), except for uses as gate operand.  *)
    VAR
      old: D.Usable;
      use, nextUse: D.Opnd;
    BEGIN
      (* 2nd operand is the old value that has to be replaced by the gate *)
      old := gate. opndList. nextOpnd. arg; 
      use := old. useList;
      WHILE (use # NIL) DO
        nextUse := use. nextUse;
        IF (use. instr # gate) & 
           Expr.Dominates (lmerge, use. instr. region) &
           use. ValueOperand() THEN
          use. ReplaceOperand (gate)
        END;
        use := nextUse
      END
    END FixupLoopGate;
  
  PROCEDURE CreateUpdate (opcode: INTEGER);
    BEGIN
      instr := region. CreateInstruction (opcode, dest. type, x. pos);
      instr. Operand (dest);
      instr. Operand (Attr.Address (region, dest, x. pos));
      instr. Operand (Expr.AccessVar (region, Sym.store));
      instr. Operand (source);
      Attr.CreateItem (y, instr, x. pos);
      AssignToVar (region, Sym.store, y);
      AddToExit (region, dest);
      dest. currValue := source
    END CreateUpdate;
  
  PROCEDURE IsCondGate (u: D.Usable): INTEGER;
  (* Returns `Opc.guardTrue' if `u' is a gate combining two true paths, and
     `Opc.guardFalse' if it is combining two false paths of a conditional OR or
     & expression.  If `u' isn't such a gate, -1 is returned.  *)
    VAR
      merge: D.Merge;
    BEGIN
      IF (u IS D.Gate) THEN
        merge := u(D.Gate). opndList. arg(D.Merge);
        IF (merge. opcode = Opc.mergeCond) THEN
          RETURN Expr.GuardClass (merge)
        END
      END;
      RETURN -1
    END IsCondGate;
  
  PROCEDURE Visible (a, b: D.Usable): BOOLEAN;
  (* Determine if `a' is visible at the place where `b' is calculated.  *)
    VAR
      aInstr: D.Instruction;
      aRegion: D.Region;
    BEGIN
      IF (a IS D.Result) THEN
        aInstr := a(D.Result). instr;
        aRegion := aInstr. region;
        IF (aInstr. opcode = Opc.gate) & (aRegion. opcode # Opc.mergeLoop) THEN
          aRegion := aRegion. region
        END;
        IF (b IS D.Result) &
           Expr.Dominates (aRegion, b(D.Result). instr. region) THEN
          RETURN TRUE
        ELSE
          (* if `a' is part of a loop, but not `b', then `a' must appear
             somewhere on the exit path of the loop; in this case `a' is
             visible at `b' when the loop is visible at `b' *)
          WHILE (aRegion # NIL)  & (aRegion. opcode # Opc.mergeLoop) DO
            aRegion := aRegion. region
          END;
          IF (aRegion = NIL) OR
             Expr.Dominates (aRegion, b(D.Result). instr. region) THEN
            RETURN FALSE
          ELSE
            RETURN Visible (aRegion, b)
          END
        END
      ELSE
        RETURN TRUE
      END
    END Visible;
  
  BEGIN
    IF (x. currValue IS D.Gate) & 
       (x. currValue(D.Gate). region. opcode = Opc.mergeLoop) &
       (x. currValue(D.Gate). region # region) THEN
      (* assign loop gate in enclosing region: use the valid value at end of 
         loop, i.e. the third operand of the gate, as source *)
      source := x. currValue(D.Gate). opndList. nextOpnd. nextOpnd. arg
    ELSE
      source := x. currValue
    END;
    
    IF (dest. mode = D.objVarPar) THEN
      CreateUpdate (Opc.updateVarParam)
      
    ELSIF ((dest. localTo # Sym.currScope) OR (dest. level = Sym.globalLevel))
          & (dest. name[0] # "$") THEN
      CreateUpdate (Opc.updateNonlocal)
      
    ELSE
      IF (source IS D.Const) OR 
         (source IS D.Gate) & 
           Expr.IsCondResult (source(D.Gate)) OR
         (source IS D.Instruction) & 
           (source(D.Instruction). opcode = Opc.notsu) OR
         (source IS D.Gate) & Expr.IsCondResult (source(D.Gate)) OR
         (source IS D.Result) & (source(D.Result). location # NIL) &
           (source(D.Result).location(D.SymLocation).attrib # D.symLocObject)OR
         (x. obj # NIL) & (x. obj. mode IN {D.objVar, D.objVarPar}) THEN
        (* add an extra copy instruction for rhs constants and variables (for
           replacement of values in loops), and some boolean instructions (to 
           keep Expr.SplitPaths from splitting this value) *)
        instr := region. CreateInstruction (Opc.copy, x. type, x. pos);
        Attr.Operand (instr, x);
        source := instr
      END;
      
      type := dest. type;
      
      (* determine merge region into which the assignment places its gate *)
      IF (region. opcode = Opc.mergeLoop) & 
         ~((source IS D.Gate) & 
           (source(D.Gate). region = region)) THEN
        merge := region(D.Merge)
      ELSE
        merge := region. merge
      END;
      
      IF (merge = NIL) THEN  (* assignment in greg, may have nonlocal effects *)
        greg := region. Greg();
        IF (dest. localTo # greg. bodyOf) OR
           (dest. mode = D.objVarPar) OR
           (greg. bodyOf. mode = D.objModule) & 
             (D.objIsUsedNonlocal IN dest. flags) OR
           (dest. name^ = "$result") THEN
          (* `dest' is a non-local variable, add its value as operand to exit 
             node, and put a reference to `dest' into its location attribute *)
          exit := greg. instrList. nextInstr;
          opnd := exit. GetOperand (dest, D.symLocObject);
          IF (opnd = NIL) THEN
            exit. Operand (source);
            exit. SetOpndSymLoc (dest)
          ELSE
            opnd. ReplaceOperand (source)
          END
        END
        
      ELSE  (* update or create gate corresponding to `dest' *)
        gate := FindGate (merge, dest);
        IF (gate = NIL) THEN               (* create new gate for `dest' *)
          gate := merge. CreateGate (Opc.gate, dest, type);
          IF (x. currValue IS D.Gate) & 
             (x. currValue(D.Gate). var = dest) THEN
            (* propagating gate into merge of enclosing region *)
            gate. oldValue := x. currValue(D.Gate). oldValue
          ELSE
            gate. oldValue := CorrectCondGate (region, dest. currValue)
          END;
          
          combined := IsCondGate (source);
          IF (combined >= 0) THEN
            (* take the value that holds in the innermost guard for the
               new gate's other value *)
            IF (combined = Opc.guardTrue) THEN
              otherValue := source(D.Gate). opndList. nextOpnd. nextOpnd. arg
            ELSE
              otherValue := source(D.Gate). opndList. nextOpnd. arg
            END;
            
            IF (x. currValue IS D.Gate) & 
               (x. currValue(D.Gate). region. opcode = Opc.mergeLoop) &
               (x. currValue(D.Gate). region # region) THEN
              (* assign loop gate in enclosing region: the valid value after
                 the loop is now in `otherValue' *)
              source := otherValue;
              otherValue := gate. oldValue
            END
          ELSE
            otherValue := gate. oldValue
          END;
          
          IF (merge. opcode = Opc.mergeCase) THEN 
            (* case merge, has arbitrary number of operands *)
            opnd := merge. opndList;
            WHILE (opnd # NIL) DO
              gate. Operand (otherValue);
              opnd := opnd. nextOpnd
            END
          ELSE                            (* all other merges have two opnds *)
            gate. Operand (otherValue);
            gate. Operand (otherValue)
          END;
          
          IF (merge = region) THEN
            (* assignment happens in a loop body: change previous uses of the
               variable to refer to the newly created gate *)
            FixupLoopGate (merge, gate);
            IF setAssignHints THEN
              (* store destination of assignment in the instruction's location
                 atribute; normally this would stay NIL *)
              gate. location := D.CreateSymLocation (dest, D.symLocObject)
            END
          END
        END;
        
        IF (source IS D.Gate) & (region. opcode = Opc.mergeCond) &
           (source(D.Gate). region. opcode = Opc.mergeCond) &
           Visible (source(D.Gate). oldValue, gate. oldValue) THEN
          (* fix old value of `gate' if source is a gate that is propagated
             from a merge-cond: into a merge-cond: *)
          gate. oldValue := source(D.Gate). oldValue
        END;
        ReplaceGateOperand (gate, region, source)
      END;
      
      IF (region. opcode = Opc.mergeLoop) &
         (source IS D.Gate) &
         (source(D.Gate). region = region) THEN
        (* don't store value in symbol table when assigning a loop gate *)
      ELSE
        dest. currValue := source
      END;
      
      IF (dest = Sym.mem) OR setAssignHints THEN
        (* store destination of assignment in the instruction's location
           atribute; normally this would stay NIL *)
        source(D.Result). location := D.CreateSymLocation (dest,D.symLocObject)
      END
    END
  END AssignToVar;

PROCEDURE AssignBoolean (region: D.Region; dest: D.Object; value: BOOLEAN);
(* Assigns constant `value' to variable `dest'.  *)
  VAR
    x: Attr.Item;
  BEGIN
    Attr.InitItem (x, S.currSymPos);
    x. type := D.struct[D.strBoolean];
    x. currValue := Sym.GetBoolConst (value);
    AssignToVar (region, dest, x)
  END AssignBoolean;

PROCEDURE ^ ReclaimFromMem (instr: D.Instruction);

PROCEDURE AssignToDesignator (region: D.Region; VAR dest, value: Attr.Item);
(* Handles assignment to structured designators that contain record fields or
   array indices.  `dest' is the target to which `value' is about to be 
   assigned.  *)
  VAR
    currDest, currValue: D.Usable;
    
  PROCEDURE AddUpdate (VAR dest, val: D.Usable);
    VAR
      type: D.Struct;
      opnd: D.Opnd;
      rvalue: D.Usable;
      access, update: D.Instruction;
      x: Attr.Item;
    BEGIN
      access := dest(D.Instruction);
      (* determine type of variable being updated *)
      rvalue := access. opndList. arg;
      WITH rvalue: D.Object DO
        type := rvalue. type
      | rvalue: D.Struct DO
        type := rvalue
      | rvalue: D.Result DO
        type := rvalue. type
      END;
      update := region. CreateInstruction (dest(D.Instruction). opcode+
                                              Opc.sizeClass, type, access.pos);
      (* add all operands of access instruction to update instruction *)
      opnd := access. opndList;
      WHILE (opnd # NIL) DO
        IF (update. opcode = Opc.updateHeap) & (opnd. nextOpnd = NIL) THEN
          (* update last operand of an update-heap instruction to the current 
             value of $store, instead of using the value from the access *)
          update. Operand (Sym.store. currValue);
          IF StdPragmas.derefCheck. true THEN
            update. flags := update. flags+{D.instrCheckNil, D.instrNotDead};
            Attr.ContainsRuntimeCheck (region)
          END
        ELSE
          update. Operand (opnd. arg);
          Attr.SetOpndPos (update, opnd. pos)
        END;
        opnd := opnd. nextOpnd
      END;
      
      update. Operand (val);
      IF (access. opcode = Opc.accessHeap) THEN (* updating heap object *)
        Attr.CreateItem (x, update, access. pos);
        AssignToVar (region, Sym.store, x);
        AddToExit (region, type)
      ELSE                               (* updating field or element *)
        dest := rvalue;
        val := update
      END
    END AddUpdate;
  
  PROCEDURE CreateUpdateMem (instr: D.Instruction);
    BEGIN
      instr. opcode := Opc.updateMem;
      instr. InsertOperand (instr. opndList, value. currValue)
    END CreateUpdateMem;
  
  BEGIN
    IF (dest. obj # NIL) THEN            (* `dest' is simple variable *)
      AssignToVar (region, dest. obj, value)
    ELSIF (dest. currValue IS D.Instruction) &
          (dest. currValue(D.Instruction). opcode = Opc.accessMem) THEN
      (* assigning to a volatile variable *)
      CreateUpdateMem (dest. currValue(D.Instruction))
    ELSIF (dest. type. form # D.strUndef) THEN
      (* if we are assigning a result of a procedure call (either function 
         result or variable parameter), the values in the access instructions 
         that described the r-value of the designator may have been rendered 
         obsolete by the side-effects of the called procedure; we have to redo
         all accesses based on the side-effects of the call *)
      Expr.RedoDesignatorAccess (region, dest);
      
      (* traverse list of `dest's access instructions for fields and elements
         backwards while adding corresponding update instructions *)
      currDest := dest. currValue;
      currValue := value. currValue;
      WHILE (currDest # dest. baseValue) &
            ((currDest(D.Instruction). opcode = Opc.accessField) OR
             (currDest(D.Instruction). opcode = Opc.accessElement)) DO
        AddUpdate (currDest, currValue)
      END;
      
      IF (dest. assignment IS D.Struct) THEN
        (* assigning to dereferenced pointer; create update-heap 
           instruction *)
        AddUpdate (currDest, currValue)
      ELSE  
        (* assigning to record or array variable *)
        Attr.InitItem (value, currValue(D.Instruction). pos);
        value. currValue := currValue;
        AssignToVar (region, dest. assignment(D.Object), value)
      END
    END
  END AssignToDesignator;

PROCEDURE CollectToMem (instr: D.Instruction);
(* Adds operands to `instr' that will force the value of $store and all local
   variables not marked with `D.objNotSideEffected' into $mem.  
   pre: last operand of `instr' is $mem.
   post: instr has operand list "... $mem $store <local-var>...' *)
  VAR
    greg: D.GlobalRegion;
    
  PROCEDURE AddOperand (localVar: D.Object);
    VAR
      obj: D.Object;
    BEGIN
      IF (localVar # NIL) THEN
        AddOperand (localVar. leftObj);
        IF (localVar. mode = D.objVar) THEN
          IF (D.objIsParameter IN localVar. flags) THEN
            (* `localVar' is a parameter and exists twice; use object from
                formal parameter list instead of the one from the procedure's
                scope *)
            obj := localVar. data(D.Object)
          ELSE
            obj := localVar
          END;
          IF ~(D.objNotSideEffected IN obj. flags) THEN
            instr. Operand (Expr.AccessVar (instr. region, obj));
            instr. SetOpndSymLoc (obj)
          END
        END;
        AddOperand (localVar. rightObj)
      END
    END AddOperand;
  
  BEGIN
    instr. Operand (Sym.store. currValue);
    instr. SetOpndSymLoc (Sym.store);
    (* add values of local variables to collecting instruction, set location 
       attributes properly *)
    greg := instr. Greg();
    AddOperand (greg. bodyOf. localDecl)
  END CollectToMem;

PROCEDURE ReclaimFromMem (instr: D.Instruction);
(* Adds results to `instr' that will retrieve the value of $store and all 
   local variables not marked with `D.objNotSideEffected' from $mem.  
   pre: last result of `instr' is $mem.
   post: instr has result list "... $mem $store <local-var>...' *)
  VAR
    greg: D.GlobalRegion;
    y: Attr.Item;

  PROCEDURE AddResult (localVar: D.Object);
    VAR
      obj: D.Object;
      x: Attr.Item;
    BEGIN
      IF (localVar # NIL) THEN
        AddResult (localVar. leftObj);
        IF (localVar. mode = D.objVar) THEN
          IF (D.objIsParameter IN localVar. flags) THEN
            (* `localVar' is a parameter and exists twice; use object from
                formal parameter list instead of the one from the procedure's
                scope *)
            obj := localVar. data(D.Object)
          ELSE
            obj := localVar
          END;
          IF ~(D.objNotSideEffected IN obj. flags) THEN
            Attr.CreateItem (x, instr. AppendResult (D.CreateSymLocation 
                         (obj, D.symLocObject), localVar. type), instr. pos);
            AssignToVar (instr. region, obj, x)
          END
        END;
        AddResult (localVar. rightObj)
      END
    END AddResult;

  BEGIN
    Attr.CreateItem (y, instr. AppendResult (D.CreateSymLocation 
                              (Sym.store, D.symLocObject), NIL), instr. pos);
    AssignToVar (instr. region, Sym.store, y);
    (* add values of local variables as results to reclaim instruction *)
    greg := instr. Greg();
    AddResult (greg. bodyOf. localDecl)
  END ReclaimFromMem;

PROCEDURE InitVariables* (region: D.Region; obj: D.Object; pos: LONGINT);
(* Initialize local variables that have `objIsInitialized' set.  *)
  VAR
    zero: D.Usable;
    x: Attr.Item;
    instr: D.Instruction;
  BEGIN
    IF (obj # NIL) THEN
      InitVariables (region, obj. leftObj, pos);
      IF (obj. mode = D.objVar) & ~(D.objIsParameter IN obj. flags) &
         (D.objIsInitialized IN obj. flags) THEN
        CASE obj. type. form OF
        | D.strBoolean: 
          zero := Sym.constFalse
        | D.strChar8..D.strReal-1, D.strByte: 
          zero := D.GetIntConst (0, obj. type)
        | D.strReal, D.strLongReal: 
          zero := D.GetRealConst (0, obj. type)
        | D.strSet8..D.strSet64:
          zero := D.GetSetConst ({}, obj. type)
        | D.strPtr, D.strPointer, D.strProc:
          zero := D.constNil
        ELSE
          instr := region. CreateInstruction (Opc.zero, obj. type, pos);
          instr. Operand (obj);
          Attr.SetOpndPos (instr, pos);
          instr. Operand (Attr.Address (region, obj, pos));
          zero := instr
        END;
        Attr.CreateItem (x, zero, pos);
        AssignToVar (region, obj, x)
      END;
      InitVariables (region, obj. rightObj, pos)
    END
  END InitVariables;



PROCEDURE Trap* (region: D.Region; opcode: INTEGER; param: D.Usable; 
                 enabled: BOOLEAN; pos: LONGINT; VAR exitInfo: Attr.ExitInfo);
  VAR
    x: Attr.Item;
    instr: D.Instruction;              
  BEGIN
    instr := region. CreateInstruction (opcode, NIL, pos);
    IF (param # NIL) THEN
      instr. Operand (param)
    END;
    IF (Sym.mem. currValue # Sym.mem) THEN
      (* only add $mem if its value has been changed previously *)
      instr. Operand (Expr.AccessVar (region, Sym.mem));
      instr. SetOpndSymLoc (Sym.mem);
      instr. Operand (Sym.store. currValue);
      instr. SetOpndSymLoc (Sym.store)
    END;
    IF enabled THEN
      Attr.ContainsRuntimeCheck (region)
    ELSE
      INCL (instr. flags, D.instrIsDisabled)
    END;
    INCL (instr. flags, D.instrNotDead);
    Attr.CreateItem (x, Sym.constTrue, pos);
    AssignToVar (region, exitInfo. trap, x);
    exitInfo. trapped := TRUE
  END Trap;

PROCEDURE ArrayCompatible (formalPar: D.Object; VAR expr: Attr.Item): BOOLEAN;
  VAR
    tf, ta: D.Struct;
  BEGIN
    IF Sym.SameType (formalPar. type, expr. type) OR
       (formalPar. mode = D.objVar) & 
         (formalPar. type. form = D.strOpenArray) &
         Sym.TypeInGroup (formalPar. type. base, D.grpChar) &
         Expr.StringConvertible (expr, formalPar. type) THEN
      RETURN TRUE
    ELSE
      tf := formalPar. type; ta := expr. type;
      WHILE (tf. form = D.strOpenArray) & 
            Sym.TypeInGroup (ta, D.grpArray) DO
        tf := tf. base; ta := ta. base
      END;
      RETURN Sym.SameType (tf, ta)
    END
  END ArrayCompatible;

PROCEDURE CheckValueParam (region: D.Region; 
                           formal: D.Object; VAR param: Attr.Item);
  VAR
    tf: D.Struct;
  BEGIN
    tf := Sym.ParameterType (formal);
    IF (tf. form = D.strOpenArray) THEN
      IF ~ArrayCompatible (formal, param) THEN
        Sym.ErrT1 (param. pos, 250, tf)
        (* not array compatible to formal parameter *)
      END
    ELSE
      AssignmentCompatible (region, tf, param)
    END
  END CheckValueParam;

PROCEDURE CheckVariableParam (id: LONGINT; formal: D.Object; 
                              VAR param: Attr.Item);
(* Tests whether the argument `param' is compatible with the variable parameter
   `formal'.  `id' is the identification of the called predefined procedure, or
   -1 for a normal procedure activation.  *)
  VAR
    tf, ta: D.Struct;
  BEGIN
    tf := Sym.ParameterType (formal); ta := param. type;
    IF ~((tf. form >= D.grpInteger) &    (* type in group *)
           Sym.TypeInGroup (ta, tf. form) OR
         Sym.SameType (tf, ta) OR        (* same types *)
         (tf. form = D.strRecord) &      (* extension of record *)
           Sym.ExtensionOf (ta, tf) OR
         (tf. form = D.strOpenArray) &   (* compatible to open array *)
           ArrayCompatible (formal, param) OR
         (tf. form = D.strOpenArray) &   (* formal ARRAY OF SYSTEM.BYTE *)
           (tf. base. form = D.strByte) OR
         (tf. form = D.strByte) &        (* formal SYSTEM.BYTE *)
           (ta. form IN {D.strChar8, D.strShortInt, D.strSet8}) OR
         (tf. form = D.strPtr) &         (* formal SYSTEM.PTR *)
           (ta. form = D.strPointer)) THEN
      Sym.ErrT1 (param. pos, 251, tf)
      (* not compatible to formal variable parameter *)
    END;
    IF (id = Sym.sysADR) THEN
      (* SYSTEM.ADR cannot be called for for constants of scalar type; but it 
         is possible to take the address of a string const or of a variable 
         imported read-only *)
      IF (param. const # NIL) & 
         ~Sym.TypeInGroup (param. type, D.grpStructured) &
         ~Sym.TypeInGroup (param. type, D.grpStringConst) THEN
        E.Err (param. pos, 235)         (* item has no address *)
      END
    ELSE
      WritableVariable (param)
    END
  END CheckVariableParam;

PROCEDURE ^ Assertion (region: D.Region; VAR cond: Attr.Item; trap: D.Const;
                       pos: LONGINT; VAR exitInfo: Attr.ExitInfo);

PROCEDURE ProcedureCall (region: D.Region; proc: Attr.Item; 
                         VAR result: Attr.Item; VAR exitInfo: Attr.ExitInfo; 
                         statement: BOOLEAN);
(* Notes on handling of actual parameters:
   For a variable passed to a variable parameter, or a designator of a 
   structured type, only the address of the variable is passed to the
   called procedure.  The callee gets the actual value from the designated
   memory location, the value isn't passed directly to the callee.  This 
   means that the value of the designator might have changed between its
   placement in the source code and the actual procedure activation.  
   Consider a procedure P(VAR x: INTEGER; y: INTEGER) called as `P(a,F())'.
   If F changes the value of `a', then `P' doesn't get the value of `a' that
   it would have without the call to `F', but rather its value after `F' has
   been completed.  Unfortunately the argument descriptor `param[0]' still 
   refers to the old, invalid value.  This is corrected by the procedure
   RedoAccess below.  *)
  CONST
    maxParameters = 64;                  (* maximum number of parameters *)
  VAR
    i, paramCount, oldErrCount: INTEGER;
    params: ARRAY maxParameters OF Attr.Item;
    copy: ARRAY maxParameters OF D.Instruction;
    str: ARRAY 16 OF CHAR;
    lastParamEnd: LONGINT;
    formal, receiver: D.Object;
    receiverCopy: D.Instruction;
    instr: D.Instruction;
    initialize, checkNil: BOOLEAN;
    poisonHeap: LONGINT;
    receiverItem: Attr.Item;
    greg: D.GlobalRegion;
  
  PROCEDURE RedoAccess (VAR x: Attr.Item; VAR copy: D.Instruction);
    BEGIN
      Expr.QueryTempCopy (x, copy, 0);
      Expr.RedoDesignatorAccess (region, x)
    END RedoAccess;
  
  PROCEDURE PredefCall (id: LONGINT); 
  (* Check if the call to a predefined procedure is correct.  *)
    VAR
      i: INTEGER;
      formal: D.Object;
    
    PROCEDURE CheckConst (i: INTEGER; min, max: LONGINT);
      BEGIN
        IF (i < paramCount) THEN
          IF (params[i]. const = NIL) THEN
            E.Err (params[i]. pos, 238)  (* has to be const expression *)
          ELSIF (params[i]. const. int < min) OR
                (params[i]. const. int > max) THEN
            E.ErrOoR (params[i]. pos, 355, min, max+1)
            (* constant parameter out of range *)
          END
        END
      END CheckConst;
    
    BEGIN
      (* check actual parameters against formal ones *)
      formal := proc. type. decl;
      i := 0;
      WHILE (i # paramCount) & (formal # NIL) DO
        IF (formal. type. form = D.strUndef) THEN (* special parameter *)
          IF (id = Sym.predMIN) OR (id = Sym.predMAX) OR 
             (id = Sym.predSIZE) OR (id = Sym.sysVAL) THEN
            IF (params[0].obj = NIL) OR (params[0]. obj. mode # D.objType) THEN
              E.Err (params[0]. pos, 182) (* data type expected *)
            ELSIF (id = Sym.predSIZE) THEN
              IF (params[0]. type. size <= 0) THEN
                E.Err (params[0]. pos, 266) (* type has no fixed size *)
              END
            ELSIF (id = Sym.sysVAL) THEN
              IF (params[0]. type. size # params[1]. type. size) THEN
                E.Err (proc. pos, -413)  
                (* warning: cast converts between types of different size *)
              ELSIF (params[0]. type. align > params[1]. type. align) THEN
                E.Err (proc. pos, -417)  
                (* warning: cast converts to type with higher alignment *)
              END
            ELSIF ~(params[0]. type. form IN {D.strChar8..D.strLongReal, 
                                              D.strSet8..D.strSet64}) THEN
              E.Err (params[0]. pos, 264) (* type has no MIN/MAX value *)
            END
          ELSIF (id = Sym.predINC) OR (id = Sym.predDEC) THEN
            IF StdPragmas.conformantMode. true THEN
              IF (params[1]. const # NIL) & 
                   ~Sym.Includes (params[0]. type, params[1]. type, D.grpNumeric) OR
                 (params[1]. const = NIL) &
                   ~Sym.SameType (params[0]. type, params[1]. type) THEN
                E.Err (params[1]. pos, 265) (* value incompatible with var *)
              END
            ELSIF ~Sym.Includes (params[0]. type, params[1]. type, D.grpNumeric) THEN
              E.Err (params[1]. pos, 265) (* value incompatible with var *)
            END
          END
        ELSIF (formal. mode = D.objVar) THEN (* value parameter *)
          Expr.CheckValue (params[i]);
          CheckValueParam (region, formal, params[i])
        ELSE                             (* variable parameter *)
          Expr.CheckValue (params[i]);
          CheckVariableParam (id, formal, params[i])
        END;
        INC (i);
        formal := formal. rightObj
      END;
      
      (* if necessary add optional parameters to some procedures *)
      IF (paramCount = 1) & (oldErrCount = E.errCount) THEN
        IF (id = Sym.predINC) OR (id = Sym.predDEC) THEN
          Attr.CreateItem (params[1], 
                   D.GetIntConst (1, D.struct[D.strShortInt]), lastParamEnd);
          INC (i); INC (paramCount); formal := formal. rightObj
        ELSIF (id = Sym.predLEN) THEN    (* LEN of dimension 0 *)
          Attr.CreateItem (params[1], 
                   D.GetIntConst (0, D.struct[D.strShortInt]), lastParamEnd);
          INC (i); INC (paramCount); formal := formal. rightObj
        ELSIF (id = Sym.predASSERT) THEN (* ASSERT without trap number *)
          Attr.CreateItem (params[1], D.GetIntConst (Config.defAssertTrap, 
                          StdTypes.IntType (Config.defAssertTrap)), lastParamEnd);
          INC (i); INC (paramCount); formal := formal. rightObj
        END
      END;
      
      IF (id = Sym.predCOPY) THEN
        (* make sure we are not copying from LONGCHAR to CHAR string *)
        IF Sym.TypeInGroup (params[0]. type, D.grpString16) &
           Sym.TypeInGroup (params[1]. type, D.grpArray) &
           (params[1]. type. base. form = D.strChar8) THEN
          Sym.ErrT1 (params[0]. pos, 268, params[1]. type)
          (* cannot copy value to array of smaller character type *)
        END
      ELSIF (id = Sym.predNEW) THEN  (* test parameters of NEW *)
        IF (D.structDisableNew IN params[0]. type. flags) THEN
          E.Err (params[0]. pos, 282)    (* can't use NEW for this type *)
        END;
        IF (D.structAbstractType IN params[0]. type. base. flags) THEN
          E.Err (params[0]. pos, 450)    (* type is abstract *)
        END;
        
        formal := Sym.NewObject ("$len", D.objVar, D.undefPos);
        formal. type := Sym.NewStruct (D.grpInteger, D.undefPos);
        WHILE (i # paramCount) & 
              (i <= params[0]. type. base. OpenDimensions()) DO
          CheckValueParam (region, formal, params[i]);
          IF (params[i]. const # NIL) &
             Sym.TypeInGroup (params[i]. type, D.grpInteger) THEN
            IF (params[i]. const. int < 0) THEN
              E.Err (params[i]. pos, 210)
              (* array length has to be non-negative *)
            ELSIF (params[i]. const. int = 0) THEN
              E.Err (params[i]. pos, -419)
              (* warning: allocating array of size zero *)
            END
          END;
          INC (i)
        END;
        IF (i > params[0]. type. base. OpenDimensions()) THEN
          formal := NIL
        END
      END;
      
      (* check required constant parameters *) 
      IF (id = Sym.predLEN) THEN
        IF (params[0]. type. base # NIL) THEN
          CheckConst (1, 0, params[0]. type. base. Dimensions())
        END
      ELSIF (id = Sym.predASSERT) THEN
        CheckConst (1, Config.minTrapNum, Config.maxTrapNum)
      ELSIF (id = Sym.predHALT) THEN
        CheckConst (0, Config.minTrapNum, Config.maxTrapNum)
      END;
      
      (* test wheter the number of actual parameters equals the number of
         formal ones *)
      IF (i # paramCount) THEN
        E.Err (params[i]. pos, 248)      (* more actual than formal params *)
      ELSIF (formal # NIL) THEN
        E.Err (lastParamEnd, 249)        (* parameter expected *)
      END
    END PredefCall;
  
  PROCEDURE PredefCodeGen (id: LONGINT); 
  (* Emit code for the call `id' to a predefined procedure.  *)
    CONST
      opcIsClass = 0; monadic = 1; moveInstr = 2; convToLong = 3; 
      assignFirst = 4; assignSecond = 5; readMem = 6; writeMem = 7; 
      secondAtEnd = 10; convToAddress = 11; checkFirst = 12;
    CONST
      typeIsFirst = -1;
      typeIsSecond = -2;
      noType = -3;
    VAR
      i: INTEGER;
      dest: SHORTINT;
      instr: D.Instruction;
      const: D.Const;
      
    PROCEDURE WriteToMem (instr: D.Instruction);
      VAR
        memAssign: Attr.Item;
      BEGIN
        Attr.CreateItem (memAssign, instr. AppendResult (D.CreateSymLocation (Sym.mem, D.symLocObject), NIL), proc. pos);
        AssignToVar (region, Sym.mem, memAssign);
        ReclaimFromMem (instr)
      END WriteToMem;
    
    PROCEDURE Instr (opc: INTEGER; formResult: SHORTINT; flags: SET);
      VAR
        type: D.Struct;
        instr: D.Instruction;
        mem: D.Usable;
      BEGIN
        IF (convToLong IN flags) THEN
          Expr.TypeConversion (region, params[0], D.strLongInt, FALSE, proc. pos)
        ELSIF (convToAddress IN flags) THEN
          Expr.TypeConversion (region, params[0], D.strAddress, FALSE, proc. pos)
        ELSIF (moveInstr IN flags) THEN
          Expr.TypeConversion (region, params[1], D.strAddress, FALSE, proc. pos);
          Expr.TypeConversion (region, params[2], D.strAddress, FALSE, proc. pos)
        END;
        IF (opcIsClass IN flags) THEN
          opc := opc*Opc.sizeClass+D.OperatorSubclass (params[0]. type, 0)
        END;
        IF (checkFirst IN flags) THEN
          RedoAccess (params[0], copy[0])
        END;
        
        CASE formResult OF
        | typeIsFirst: type := params[0]. type
        | typeIsSecond: type := params[1]. type
        | noType: type := NIL
        ELSE
          type := D.struct[formResult]
        END;
        IF (readMem IN flags) THEN
          mem := Expr.AccessVar (region, Sym.mem)
        ELSE 
          mem := NIL
        END;
        instr := region. CreateInstruction (opc, type, proc. pos);
        
        Attr.Operand (instr, params[0]);
        IF ~(monadic IN flags) & ~(secondAtEnd IN flags) THEN
          Attr.Operand (instr, params[1])
        END;
        IF (moveInstr IN flags) THEN
          Attr.Operand (instr, params[2])
        END;
        IF (readMem IN flags) THEN
          instr. Operand (mem);
          instr. SetOpndSymLoc (Sym.mem);
          CollectToMem (instr)
        END;
        IF (secondAtEnd IN flags) THEN
          Attr.Operand (instr, params[1])
        END;
        Expr.EvalInstr (result, instr);
        
        IF (assignFirst IN flags) THEN
          AssignToDesignator (region, params[0], result)
        ELSIF (assignSecond IN flags) THEN
          AssignToDesignator (region, params[1], result)
        END;
        IF (writeMem IN flags) THEN
          WriteToMem (instr)
        END
      END Instr;
    
    BEGIN
      result := params[0];
      CASE id OF
      | Sym.predCHR, Sym.predLONGCHR, Sym.predENTIER, Sym.predLONG, 
        Sym.predSHORT, Sym.predORD:
        (* type conversion operator *)
        IF (id = Sym.predLONG) THEN
          dest := params[0]. type. form+1
        ELSIF (id = Sym.predSHORT) THEN
          dest := params[0]. type. form-1
        ELSIF (id = Sym.predORD) THEN
          dest := params[0]. type. form+(D.strInteger - D.strChar8)
        ELSE
          dest := proc. type. base. form
        END;
        Expr.TypeConversion (region, params[0], dest, TRUE, proc. pos);
        result := params[0]
      | Sym.predABS:
        Instr (Opc.classAbs, typeIsFirst, {opcIsClass, monadic})
      | Sym.predASH:
        Instr (Opc.classAsh, D.strLongInt, {opcIsClass, convToLong})
      | Sym.predCAP:
        Instr (Opc.classCap, params[0]. type. form, {opcIsClass, monadic})
      | Sym.predLEN:
        Attr.ArrayLength (region, params[0], SHORT (params[1]. const. int), 
                          proc. pos, TRUE, result)
      | Sym.predMAX:
        Attr.CreateItem (result, StdTypes.Max (result. type. form), proc. pos)
      | Sym.predMIN:
        Attr.CreateItem (result, StdTypes.Min (result. type. form), proc. pos)
      | Sym.predODD:
        Instr (Opc.classOdd, D.strBoolean, {opcIsClass, monadic})
      | Sym.predSIZE:
        const := D.GetIntConst (result. type. size, 
                 StdTypes.IntType (result. type. size));
        Attr.CreateItem (result, const, proc. pos)
        
      | Sym.sysADR:
        Attr.CreateItem (result, Attr.Adr (region, result), proc. pos);
        result. type := D.struct[D.strAddress]
      | Sym.sysBIT:
        Instr (Opc.bit, D.strBoolean, {convToAddress, readMem})
      | Sym.sysLSH:
        Instr (Opc.classLsh, typeIsFirst, {opcIsClass})
      | Sym.sysROT:
        Instr (Opc.classRot, typeIsFirst, {opcIsClass})
      | Sym.sysVAL:
        instr := region. CreateInstruction (Opc.typeCast, result. type, proc. pos);
        Attr.Operand (instr, params[1]);
        IF (params[1]. obj # NIL) THEN
          instr. SetOpndSymLoc (params[1]. obj)
        END;
        Expr.EvalInstr (result, instr);
        result. adr := Attr.Adr (region, params[1])
        
      | Sym.predASSERT:
        Assertion (region, result, params[1]. const, proc. pos, exitInfo)
      | Sym.predCOPY:
        instr := region. CreateInstruction (Opc.stringCopy, params[1]. type, proc. pos);
        Attr.Operand (instr, params[1]);
        instr. Operand (Attr.Adr (region, params[1]));
        IF Attr.HasLengthInfo (params[1], 0) THEN
          Attr.ArrayLength (region, params[1], 0, params[1]. pos, FALSE, result);
          Attr.Operand (instr, result)
        ELSE
          instr. Operand (D.GetIntConst (StdTypes.maxLongInt, D.struct[D.strLongInt]))
        END;
        Attr.Operand (instr, params[0]);
        instr. Operand (Attr.Adr (region, params[0]));
        Attr.CreateItem (result, instr, proc. pos);
        AssignToDesignator (region, params[1], result)
      | Sym.predDEC:
        Expr.TypeConversion (region, params[1], params[0]. type. form,
                             FALSE, params[1]. pos);
        Instr (Opc.classSub, typeIsFirst, {opcIsClass, assignFirst, checkFirst})
      | Sym.predEXCL:
        Expr.BoundSetElement (region, params[0]. type. form, params[1]);
        Instr (Opc.classBitClear, typeIsFirst, {opcIsClass, assignFirst, checkFirst})
      | Sym.predHALT:
        Trap (region, Opc.trapHalt, params[0]. const, TRUE, proc.pos, exitInfo)
      | Sym.predINC:
        Expr.TypeConversion (region, params[1], params[0]. type. form,
                             FALSE, params[1]. pos);
        Instr (Opc.classAdd, typeIsFirst, {opcIsClass, assignFirst, checkFirst})
      | Sym.predINCL:
        Expr.BoundSetElement (region, params[0]. type. form, params[1]);
        Instr (Opc.classBitSet, typeIsFirst, {opcIsClass, assignFirst, checkFirst})
      | Sym.predNEW:
        instr := region. CreateInstruction (Opc.new, params[0]. type, proc. pos);
        INCL (instr. flags, D.instrUniqueResult);
        IF initialize THEN
          INCL (instr. flags, D.instrInitialize)
        END;
        IF (poisonHeap >= 0) THEN
          INCL (instr. flags, D.instrPoisonHeap)
        END;
        RedoAccess (params[0], copy[0]);
        instr. Operand (params[0]. type. base);
        FOR i := 1 TO paramCount-1 DO
          Attr.Operand (instr, params[i])
        END;
        Attr.CreateItem (result, instr, proc. pos);
        AssignToDesignator (region, params[0], result)
      
      | Sym.sysGET:
        Instr (Opc.accessMem, typeIsSecond,
               {convToAddress, monadic, assignSecond, readMem})
      | Sym.sysPUT:
        Instr (Opc.updateMem, noType, 
               {convToAddress, readMem, writeMem})
      | Sym.sysMOVE:
        Instr (Opc.move, noType, {moveInstr, readMem, writeMem}) 
      | Sym.sysNEW:
        instr := region. CreateInstruction (Opc.newBlock, params[0]. type, proc. pos);
        INCL (instr. flags, D.instrUniqueResult);
        IF initialize THEN
          INCL (instr. flags, D.instrInitialize)
        END;
        IF (poisonHeap >= 0) THEN
          INCL (instr. flags, D.instrPoisonHeap)
        END;
        RedoAccess (params[0], copy[0]);
        Attr.Operand (instr, params[1]);
        Attr.CreateItem (result, instr, proc. pos);
        AssignToDesignator (region, params[0], result)
      END
    END PredefCodeGen;
    
  PROCEDURE SetSideEffectFlags (localVar: D.Object; set: BOOLEAN);
  (* Clear or set the flag `D.objNotSideEffected' for all local variables of
     the current procedure.  *)
    VAR
      obj: D.Object;
    BEGIN
      IF (localVar # NIL) THEN
        SetSideEffectFlags (localVar. leftObj, set);
        IF (localVar. mode = D.objVar) THEN
          IF (D.objIsParameter IN localVar. flags) THEN
            (* `localVar' is a parameter and exists twice; use object from
                formal parameter list instead of the one from the procedure's
                scope *)
            obj := localVar. data(D.Object)
          ELSE
            obj := localVar
          END;
          IF set THEN
            EXCL (obj. flags, D.objNotSideEffected)
          ELSE
            INCL (obj. flags, D.objNotSideEffected)
          END
        END;
        SetSideEffectFlags (localVar. rightObj, set)
      END
    END SetSideEffectFlags;
  
  PROCEDURE PassParameters (instr: D.Instruction; receiver: D.Object);
    VAR
      i: INTEGER;
      formal: D.Object;
    
    PROCEDURE PassParameter (formal: D.Object; VAR param: Attr.Item);
      VAR
        j: INTEGER;
        len, size: Attr.Item;
        
      PROCEDURE SetSymLoc (attr: INTEGER);
        VAR
          opnd: D.Opnd;
        BEGIN
          opnd := instr. LastOperand();
          IF (attr = MIN (INTEGER)) THEN  (* use actual param *)
            opnd. location := D.CreateSymLocation (param. obj, D.symLocObject)
          ELSE  (* use formal param *)
            opnd. location := D.CreateSymLocation (formal, attr)
          END
        END SetSymLoc;
      
      BEGIN
        Attr.Operand (instr, param); (* variable's value *)
        IF (formal. mode = D.objVarPar) & (param. obj # NIL) &
           (param. obj. mode = D.objVar) & 
           (param. obj. localTo = Sym.currScope) THEN
          (* directly passing local variable to var parameter: use the actual
             parameter's location instead of the one of the formal parameter *)
          SetSymLoc (MIN (INTEGER))
        ELSE
          SetSymLoc (D.symLocObject)
        END;
        IF StdTypes.PassPerReference (formal, TRUE) THEN
          instr. Operand (Attr.Adr (region, param)); (* address *)
          SetSymLoc (D.symLocAddress)
        END;
        IF (formal. mode = D.objVarPar) & 
           (formal. type. form = D.strRecord) THEN (* pass type tag *)
          IF ~(D.objNoTypeTag IN formal. flags) THEN
            instr. Operand (Attr.TypeTag (region, param, -1));
            SetSymLoc (D.symLocTypeTag)
          END
        ELSIF (formal. type. form = D.strOpenArray) &
              (formal. type. base. form = D.strByte) THEN
          (* formal parameter is an ARRAY OF BYTE: pass size in bytes *)
          IF ~(D.objNoLengthTag IN formal. flags) THEN
            Attr.SizeOfItem (region, param, 0, param. pos, size);
            Attr.Operand (instr, size);
            SetSymLoc (D.symLocLength0)
          END
        ELSE                               (* open array length info *)
          IF ~(D.objNoLengthTag IN formal. flags) THEN
            FOR j := 0 TO formal. type. OpenDimensions()-1 DO
              Attr.ArrayLength (region, param, j, param. pos, FALSE, len);
              Attr.Operand (instr, len);
              SetSymLoc (j)
            END
          END
        END
      END PassParameter;
    
    BEGIN
      (* provide operands for procedure's receiver *)
      IF (receiver # NIL) THEN
        PassParameter (receiver, receiverItem)
      END;
      
      (* provide operands for procedure's formal parameters *)
      IF (proc. type. decl # NIL) THEN
        i := 0;
        formal := proc. type. decl;
        WHILE (formal # NIL) & (formal. mode # D.objRestParam) DO
          PassParameter (formal, params[i]);
          formal := formal. rightObj;
          INC (i)
        END;
        (* pass actual parameter(s) of `three dots' as values only *)
        WHILE (i # paramCount) DO
          instr. Operand (params[i]. currValue);
          INC (i)
        END
      END
    END PassParameters;
  
  PROCEDURE PassNonlocalReferences (instr: D.Instruction);
    VAR
      enter: D.Instruction;
      res: D.Result;
      x, len: Attr.Item;
      opnd: D.Opnd;
      struct: D.Struct;
      accessStore, accessMem: BOOLEAN;
    BEGIN  (* provide values for nonlocal accesses *)
      IF (proc. obj = NIL) OR (proc. obj. mode # D.objProc) OR
         (proc. obj. greg = NIL) THEN
        enter := NIL
      ELSE
        enter := proc. obj. greg. EnterInstr()
      END;
      
      IF (enter = NIL) THEN
        instr. Operand (Expr.AccessVar (region, Sym.mem));
        instr. SetOpndSymLoc (Sym.mem);
        CollectToMem (instr)
      ELSE
        (* find end of parameters in result list of enter instruction *)
        res := enter. nextResult;
        WHILE (res # NIL) &
              ~(res. location(D.SymLocation). var IS D.Struct) &
              (res. location(D.SymLocation). var(D.Object). localTo =
                                                                  proc. obj) DO
          res := res. nextResult
        END;
        accessStore := FALSE;
        accessMem := FALSE;
        
        (* add a new operand for each additional parameter *)
        WHILE (res # NIL) DO
          IF (res. location # NIL) & 
             (res. location(D.SymLocation). attrib # D.symLocObject) THEN
            (* access to additional attributes (type tag, length, address) of
               a nonlocal (to the called procedure) variable *)
            CASE res. location(D.SymLocation). attrib OF
            | D.symLocTypeTag:
              Attr.InitItem (x, instr. pos);
              x. ttHint := res. location(D.SymLocation). var;
              instr. Operand (Attr.TypeTag (region, x, -1))
            | D.symLocAddress:
              instr. Operand (Attr.Address (region, 
                                res. location(D.SymLocation). var, instr. pos))
            ELSE  (* >= D.symLocLength0 *)
              Attr.InitItem (x, instr. pos);
              x. type := res. location(D.SymLocation). var(D.Object). type;
              x. ttHint := res. location(D.SymLocation). var;
              x. assignment := res. location(D.SymLocation). var;
              x. arrayDim := 0;
              Attr.ArrayLength (region, x, res. location(D.SymLocation).attrib,
                                instr. pos, FALSE, len);
              Attr.Operand (instr, len)
            END
          ELSIF (res. location(D.SymLocation). var IS D.Struct) THEN
            (* called procedure uses heap object *)
            struct := res. location(D.SymLocation). var(D.Struct);
            instr. Operand (struct);
            Expr.AddStructToEnter (region, struct);
            accessStore := TRUE
          ELSE
            instr. Operand (Expr.AccessVar (region, 
                                 res. location(D.SymLocation). var(D.Object)));
            IF (res. location(D.SymLocation). var = Sym.mem) THEN
              accessMem := TRUE
            ELSIF Attr.PartOfStore (Sym.currScope, res. location) THEN
              accessStore := TRUE
            END
          END;
          Attr.SetOpndPos (instr, proc. pos);
          IF (res. location # NIL) THEN
            opnd := instr. LastOperand();
            opnd. location := res. location
          END;
          res := res. nextResult
        END;
        
        (* if the called procedure accesses objects on the heap without reading
           from $mem, then add the current value of $store to its operands *)
        IF accessMem THEN
          CollectToMem (instr)
        ELSIF accessStore THEN
          instr. Operand (Expr.AccessVar (region, Sym.store));
          instr. SetOpndSymLoc (Sym.store)
        END
      END
    END PassNonlocalReferences;
  
  PROCEDURE RegisterSideEffects (instr: D.Instruction);
    VAR
      exit, memDummy: D.Instruction;
      opnd: D.Opnd;
      res, resDummy: D.Result;
      var: D.Addressable;
      x: Attr.Item;
      updateStore, updateMem: BOOLEAN;
      resMem: D.Result;
    
    PROCEDURE WritesToMem (exit: D.Instruction; VAR opnd: D.Opnd): BOOLEAN;
      BEGIN
        opnd := exit. opndList;
        WHILE (opnd # NIL) DO
          IF (opnd. location # NIL) &
             (opnd. location(D.SymLocation). var = Sym.mem) THEN
            RETURN TRUE
          END;
          opnd := opnd. nextOpnd
        END;
        RETURN FALSE
      END WritesToMem;
    
    PROCEDURE OpndLoc (VAR x: Attr.Item): D.Location;
    (* If `x' is a variable, then return the location attribute of that 
       variable.  Otherwise return NIL.
       pre: `x' is a designator that was passed to a variable parameter and has
         been modified by the procedure call.  *)
      BEGIN
        IF (x. obj # NIL) & (x. obj. mode = D.objVar) &
           (x. obj. localTo = Sym.currScope) THEN
          RETURN D.CreateSymLocation (x. obj, D.symLocObject)
        ELSE
          RETURN NIL
        END
      END OpndLoc;
    
    BEGIN  (* assign side effects to their variables *)
      IF (proc. obj = NIL) OR (proc. obj. greg = NIL) THEN
        exit := NIL
      ELSE
        exit := proc. obj. greg. ExitInstr()
      END;
      
      IF (proc. obj = NIL) OR (proc. obj. mode # D.objProc) OR
         (proc. obj. greg = NIL) OR (proc. obj. greg. EnterInstr() = NIL) THEN
        (* no enter instruction: procedure is imported and has no explicit 
           side-effect information; no side-effect info is available for 
           type-bound procs (at this level), since the called procedure may
           differ from the statically dtermined one
           therefore we conservatively assume that the called procedure assigns
           to $mem, i.e. it has arbitrary side-effects *)
        Attr.InitItem (x, instr. pos);
        x. currValue := instr. AppendResult (NIL, D.struct[D.strUndef]);
        AssignToVar (region, Sym.mem, x);
        ReclaimFromMem (instr)
      
      ELSIF (exit = NIL) THEN
        (* the called procedure has no exit instruction; this means it is never
           left, e.g. due to an endless loop or a HALT; tell dead code 
           elimination to leave this call alone *)
        INCL (instr. flags, D.instrNotDead)
        
      ELSE                               (* register nonlocal assignments *)
        Attr.InitItem (x, proc. pos);
        updateStore := FALSE;
        updateMem := FALSE;
        
        IF WritesToMem (exit, opnd) THEN
          (* execute write to $mem and reclaim all local variables from it; 
             preliminary result, replaced later *)
          memDummy := region. CreateInstruction (-1, NIL, D.undefPos);
          resMem := memDummy. AppendResult (opnd. location, Sym.mem. type);
          x. currValue := resMem;
          AssignToVar (region, Sym.mem, x);
          ReclaimFromMem (memDummy);
          updateMem := TRUE
        ELSE
          resMem := NIL
        END;
        
        opnd := exit. opndList;
        WHILE (opnd # NIL) DO
          var := opnd. location(D.SymLocation). var;
          
          WITH var: D.Object DO
            IF (var. localTo # proc. obj) THEN  (* variable outside `proc' *)
              IF (var. localTo # Sym.currScope) THEN
                updateStore := TRUE
              END;
            
              x. currValue := instr. AppendResult (opnd. location, var.type);
              IF (D.objIsTwisted IN var. flags) THEN
                E.ErrIns (proc. pos, -416, var. name^)
                (* warning: call may change guarded variable *)
              END;
              IF (var = Sym.mem) THEN  (* integrate $mem value *)
                resMem. ReplaceUses (x. currValue);
                Sym.mem. currValue := x. currValue
              ELSE
                AssignToVar (region, var, x)
              END
              
            ELSIF (var. name^ = "$result") THEN (* function result *)
              result. currValue := instr
              
            ELSE  (* `var' denotes a variable parameter *)
              IF (var = receiver) THEN
                res := instr. AppendResult (OpndLoc (receiverItem), receiverItem. type)
              ELSE
                i := 0;
                formal := proc. type. decl;
                WHILE (formal # var) DO
                  INC (i);
                  formal := formal. rightObj
                END;
                res := instr. AppendResult (OpndLoc (params[i]), params[i]. type)
              END;
              res. info := opnd
            END
            
          | var: D.Struct DO             (* heap object was modified *)
            resDummy := instr. AppendResult (opnd. location, NIL);
            AddToExit (region, var);
            updateStore := TRUE
          END;

          opnd := opnd. nextOpnd
        END;
        IF (resMem # NIL) THEN
          instr. MoveResultList (resMem);
          resMem.  instr. Delete()
        END;
        
        res := instr. nextResult;
        opnd := exit. opndList;
        WHILE (opnd # NIL) DO
          var := opnd. location(D.SymLocation). var;
          
          WITH var: D.Object DO
            IF (var. localTo = proc. obj) & (var. name^ # "$result") THEN
              (* variable parameter is modified; identify the designator that
                 was passed to it and assign the new value to it *)
              WHILE (res. info # opnd) DO
                res := res. nextResult
              END;
              res. info := NIL;
              IF (var = receiver) THEN
                x. currValue := res;
                RedoAccess (receiverItem, receiverCopy);
                AssignToDesignator (region, receiverItem, x)
              ELSE
                i := 0;
                formal := proc. type. decl;
                WHILE (formal # var) DO
                  INC (i);
                  formal := formal. rightObj
                END;
                x. currValue := res;
                RedoAccess (params[i], copy[i]);
                AssignToDesignator (region, params[i], x)
              END
            END
          ELSE  (* ignore *)
          END;

          opnd := opnd. nextOpnd
        END;
        
        (* if the called procedure updates objects on the heap without writing
           to $mem, then add a new value for $store to its results *)
        IF updateStore & ~updateMem THEN
          IF (instr. GetOperand (Sym.store, D.symLocObject) = NIL) THEN
            (* we have no operand taking $store, so we need to add one *)
            instr. Operand (Expr.AccessVar (instr. region, Sym.store));
            instr. SetOpndSymLoc (Sym.store);
          END;
          x. currValue := instr. AppendResult (D.CreateSymLocation (Sym.store, D.symLocObject), NIL);
          AssignToVar (region, Sym.store, x)
        END
      END;
      
      IF (proc. obj # NIL) & (proc. obj. mode = D.objProc) &
         (proc. obj. greg # NIL) & (proc. obj. greg. enter # NIL) & 
         (D.instrNotDead IN proc. obj. greg. enter. flags) THEN
        (* evaluation of the called procedure may raise an exception; make sure
           that the procedure is never mistaken for dead code *)
        INCL (instr. flags, D.instrNotDead)
      END
    END RegisterSideEffects;
  
  PROCEDURE MarkSideEffectedVars (receiver: D.Object);
  (* Scans the argument list of the procedure call for addresses of local
     variables (this includes local value parameters).  If such an address is
     encountered, then it is made sure the variable appears in the collect 
     or reclaim instruction (if these exists).  *)
    VAR
      i: INTEGER;
      res: D.Result;
      enter, exit: D.Instruction;
      formal, obj: D.Object;
    
    PROCEDURE CheckParameter (formal: D.Object; VAR param: Attr.Item);
      BEGIN
        IF (formal. mode = D.objVarPar) & 
           (param. assignment # NIL) &
           (param. assignment IS D.Object) &
           (param. assignment(D.Object). mode = D.objVar) &
           (param. assignment(D.Object). localTo = Sym.currScope) THEN
          EXCL (param. assignment(D.Object). flags, D.objNotSideEffected)
        END
      END CheckParameter;
    
    PROCEDURE CheckIfAdr (value: D.Usable);
      VAR
        obj: D.Object;
      BEGIN
        IF (value IS D.Instruction) &
           (value(D.Instruction). opcode = Opc.adr) &
           (value(D.Instruction). opndList. arg IS D.Object) THEN
          obj := value(D.Instruction). opndList. arg(D.Object);
          IF (obj. mode = D.objVar) & (obj. localTo = Sym.currScope) THEN
            EXCL (obj. flags, D.objNotSideEffected)
          END
        END
      END CheckIfAdr;
    
    PROCEDURE HasForwardDecl (localDecl: D.Object): BOOLEAN;
      BEGIN
        IF (localDecl # NIL) THEN
          IF (localDecl. mode = D.objProc) &
             (localDecl. flags * {D.objIsForwardDecl, D.objWasForwardDecl} # {}) THEN
            RETURN TRUE
          ELSE
            RETURN HasForwardDecl (localDecl. leftObj) OR
                   HasForwardDecl (localDecl. rightObj)
          END
        ELSE
          RETURN FALSE
        END
      END HasForwardDecl;
    
    BEGIN
      (* first check if the called procedure is nested into the current one; if
         the current procedure contains local forward declarations, and the 
         called procedure accesses $mem, then assume that it can read/write
         any variable of the caller, either directly or indirectly; keep in 
         mind that the level of the current scope is one too high until 
         Sym.CloseScope has been called;
         all local variables are also visible if we are currently within a 
         module body or the called procedure is taken from a variable *)
      IF (proc. obj = NIL) OR (proc. obj. mode # D.objProc) THEN
        (* calling a procedure variable or a type-bound procedure; only global
           variables are visible to the callee, and any of them might be 
           changed; if we are inside a local procedure the usual criterias
           further down apply *)
        IF (Sym.currScope. level = Sym.globalLevel) THEN
          SetSideEffectFlags (Sym.currScope. localDecl, TRUE);
          RETURN
        END
      ELSIF (((proc. obj. level >= Sym.currScope. level) & 
              HasForwardDecl (Sym.currScope. localDecl)) OR
             (Sym.currScope. level = Sym.globalLevel)) &
            (proc. obj. greg # NIL) THEN
        enter := proc. obj. greg. EnterInstr();
        exit := proc. obj. greg. ExitInstr();
        IF (enter # NIL) & 
             (enter. GetResult (Sym.mem, D.symLocObject) # NIL) OR
           (exit # NIL) & 
             (exit. GetOperand (Sym.mem, D.symLocObject) # NIL) THEN
          SetSideEffectFlags (Sym.currScope. localDecl, TRUE);
          RETURN
        END
      END;
      
      (* scan formal parameters *)
      IF (receiver # NIL) THEN
        CheckParameter (receiver, receiverItem);
        CheckIfAdr (receiverItem. currValue)
      END;
      IF (proc. type. decl # NIL) THEN
        i := 0;
        formal := proc. type. decl;
        WHILE (formal # NIL) & (formal. mode # D.objRestParam) DO
          CheckParameter (formal, params[i]);
          formal := formal. rightObj;
          INC (i)
        END;
        FOR i := 0 TO paramCount-1 DO
          CheckIfAdr (params[i]. currValue)
        END
      END;
      
      IF (proc. obj # NIL) & (proc. obj. mode = D.objProc) &
         (proc. obj. greg # NIL) THEN
        enter := proc. obj. greg. EnterInstr();
        (* scan arguments describing nonlocal side-effects *)
        IF (enter # NIL) THEN
          res := enter. nextResult;
          WHILE (res # NIL) DO
            IF (res. location(D.SymLocation). var IS D.Object) THEN
              obj := res. location(D.SymLocation). var(D.Object);
              IF (obj. localTo = Sym.currScope) &
                 (res. location(D.SymLocation). attrib = D.symLocAddress) THEN
                EXCL (obj. flags, D.objNotSideEffected)
              ELSE  
                (* check if the variable holds an address of a local var *)
                CheckIfAdr (obj. currValue)
              END
            END;
            res := res. nextResult
          END
        END
      END
    END MarkSideEffectedVars;
  
  BEGIN
    exitInfo. returned := FALSE;
    exitInfo. exited := FALSE;
    exitInfo. trapped := FALSE;
    Attr.InitItem (result, proc. pos);
    oldErrCount := E.errCount;
    
    IF (proc. type. form # D.strProc) THEN
      Sym.ErrT1 (proc. pos, 247, proc. type); (* not a procedure *)
      result. type := D.struct[D.strUndef]
    ELSE 
      IF statement & (proc. type. base. form # D.strNone) THEN
        E.Err (proc. pos, 252)           (* not a proper procedure *)
      ELSIF ~statement & (proc. type. base. form = D.strNone) THEN
        E.Err (proc. pos, 253)           (* not a function procedure *)
      END;
      result. type := proc. type. base
    END;
    IF ~statement & (S.sym # S.lParen) THEN
      E.Err (S.lastSymEnd, 130)          (* `(' expected *)
    END;
    IF (proc. obj # NIL) & (proc. obj. mode = D.objTBProc) THEN
      receiver := proc. obj. data(D.Object);
      receiverItem := Expr.receiverDesignator;
      receiverCopy := Expr.InsertTempCopy (region, receiverItem)
    ELSE
      receiver := NIL;
      receiverCopy := NIL
    END;
    
    initialize := StdPragmas.initialize. true;
    checkNil := StdPragmas.derefCheck. true;
    poisonHeap := StdPragmas.poisonHeap. value;
    paramCount := 0;
    (* read actual parameter list *)
    IF (S.sym < S.semicolon) THEN
      S.CheckSym (S.lParen);
      IF (S.sym = S.rParen) THEN
        lastParamEnd := S.currSymPos
      ELSE
        Expr.Expr (region, params[paramCount]);
        copy[paramCount] := Expr.InsertTempCopy (region, params[paramCount]);
        INC (paramCount);
        WHILE (S.sym=S.comma) OR (S.lParen<=S.sym) & (S.sym<=S.ident) DO
          S.CheckSym (S.comma);
          IF (paramCount = maxParameters) THEN
            IntStr.IntToStr (maxParameters, str);
            E.ErrIns (S.currSymPos, 246, str);
            (* too many parameters (maximum is `maxParameters') *)
            DEC (paramCount)
          END;
          Expr.Expr (region, params[paramCount]);
          copy[paramCount] := Expr.InsertTempCopy (region, params[paramCount]);
          INC (paramCount)
        END;
        lastParamEnd := S.lastSymEnd
      END;
      S.CheckSym (S.rParen)
    ELSE
      lastParamEnd := S.lastSymEnd
    END;
    
    (* if necessary adjust current value of parameter variables, but do not
       remove the copy instructions *)
    IF (receiver # NIL) THEN
      Expr.QueryTempCopy (receiverItem, receiverCopy, 0)
    END;
    FOR i := 0 TO paramCount-1 DO
      Expr.QueryTempCopy (params[i], copy[i], 0)
    END;
    
    IF (proc. type. form = D.strProc) & (proc. obj # NIL) &
       (proc. obj. data # NIL) & (proc. obj. data IS D.Const) &
       ~(D.objIsSpecialCodeProc IN proc. obj. flags) THEN
      PredefCall (proc. obj. data(D.Const). int);
      IF (E.errCount = oldErrCount) THEN (* no error in call, construct call *)
        PredefCodeGen (proc. obj. data(D.Const). int)
      END
    ELSIF (proc. type. form = D.strProc) THEN
      IF (receiver # NIL) & (receiver. type. form = D.strRecord) THEN
        RedoAccess (receiverItem, receiverCopy)
      END;

      (* check actual parameters against formal ones *)
      formal := proc. type. decl;
      i := 0;
      WHILE (i # paramCount) & (formal # NIL) & 
            (formal. mode # D.objRestParam) DO
        Expr.CheckValue (params[i]);
        IF (D.objIsTwisted IN formal. flags) & (formal. localDecl = NIL) THEN
          E.Err (params[i]. pos, -411)       
          (* warning: formal parameter type modified by WITH statement *)
        END;
        IF StdTypes.PassPerReference (formal, TRUE) &
           (params[i]. const = NIL) THEN
          RedoAccess (params[i], copy[i])
        END;
        IF (D.objNilCompat IN formal. flags) &
           (params[i]. const = D.constNil) THEN
          (* passing NIL to a parameter of a C procedure that has the
             NIL_COMPAT modifier set *)
          params[i]. adr := D.constNil
        ELSIF (formal. mode = D.objVar) THEN (* value parameter *)
          CheckValueParam (region, formal, params[i])
        ELSE                             (* variable parameter *)
          CheckVariableParam (-1, formal, params[i])
        END;
        INC (i);
        formal := formal. rightObj
      END;
      (* test whether the number of actual parameters equals the number of
         formal ones *)
      IF (formal # NIL) & (formal. mode = D.objRestParam) THEN
        (* three dots `...' parameter, skip checks for rest of params *)
      ELSIF (i # paramCount) THEN
        E.Err (params[i]. pos, 248)     (* more actual than formal params *)
      ELSIF (formal # NIL) THEN
        E.Err (lastParamEnd, 249)       (* parameter expected *)
      END;
      
      IF (E.errCount = oldErrCount) THEN (* no error in call, construct call *)
        greg := region. Greg();
        SetSideEffectFlags (Sym.currScope. localDecl, FALSE);
        MarkSideEffectedVars (receiver);
        
        instr := region. CreateInstruction (Opc.call, result. type, proc. pos);
        result. currValue := instr;
        (* append address of entry point *)
        IF (proc. obj # NIL) & (proc. obj. mode = D.objTBProc) THEN
          (* call of type-bound procedure *)
          instr. Operand (proc. adr)
        ELSE  (* take the designator's value as entry point *)
          instr. Operand (proc. currValue);
          IF checkNil &
             (~(proc. currValue IS D.Instruction) OR
              (proc. currValue(D.Instruction). opcode # Opc.adr)) THEN
            INCL (instr. flags, D.instrCheckNil);
            Attr.ContainsRuntimeCheck (region) 
          END
        END;
        instr. Operand (proc. type);  (* formal parameter type *)
        (* add reference to procedure object *)
        IF (proc. obj # NIL) & 
           (proc. obj. mode IN {D.objProc, D.objTBProc}) THEN
          instr. Operand (proc. obj)
        ELSE  (* `proc' is the value of a procedure variable *)
          instr. Operand (D.constUndef)
        END;
        PassParameters (instr, receiver);
        PassNonlocalReferences (instr);
        RegisterSideEffects (instr);
        
        SetSideEffectFlags (Sym.currScope. localDecl, TRUE)
      END
    END;
    
    (* remove temporary copies *)
    IF (receiver # NIL) THEN
      Expr.QueryTempCopy (receiverItem, receiverCopy, 2)
    END;
    FOR i := 0 TO paramCount-1 DO
      Expr.QueryTempCopy (params[i], copy[i], 2)
    END;
    
    IF ~statement & (result. currValue = NIL) THEN  (* create dummy result *)
      result. currValue := D.GetIntConst (1, D.struct[D.strShortInt]);
      result. type := D.struct[D.strUndef]
    END
  END ProcedureCall;



PROCEDURE CommitIfMerge (merge: D.Region);
  VAR
    use: D.Opnd;
    gate: D.Gate;
    x: Attr.Item;
  BEGIN
    use := merge. useList;
    WHILE (use # NIL) DO
      IF (use. instr IS D.Gate) & (use. instr(D.Gate). var # NIL) THEN
        gate := use. instr(D.Gate);
        Attr.InitItem (x, S.currSymPos);
        x. currValue := gate;
        AssignToVar (merge. region, gate. var, x)
      END;
      use := use. nextUse
    END
  END CommitIfMerge;

PROCEDURE FixupCondPath (path: D.Region; oldMerge: D.Merge; 
                         merge: D.Merge; innerMost: BOOLEAN);
(* Propagates gates from paths into a merge-cond into the merge.  The path
   can be a merge-cond itself, or a region guarded against true/true or
   false/false.  *)
  VAR
    use: D.Opnd;
    gate: D.Gate;
    x: Attr.Item;
    opn, searchFor: INTEGER;
    instr: D.Instruction;
  BEGIN
    IF (oldMerge # NIL) THEN
      opn := oldMerge. ArgumentIndex (path)+1;
      use := oldMerge. useList;
      WHILE (use # NIL) DO
        IF (use. instr IS D.Gate) & (use. instr(D.Gate). var # NIL) THEN
          gate := use. instr(D.Gate);
          Attr.InitItem (x, S.currSymPos);
          x. currValue := gate. NthArgument (opn);
          AssignToVar (path, gate. var, x)
        END;
        use := use. nextUse
      END;
      
      IF (merge # NIL) & (merge. region # oldMerge. region) THEN
        (* we are replacing the merge; if there are any variables that should 
           be propagated in addition to the gates, do some assignments to 
           move the values along *)
        instr := oldMerge. instrList;
        WHILE (instr # NIL) DO
          IF (instr. opcode = Opc.noopGateHint) THEN
            Attr.InitItem (x, S.currSymPos);
            x. currValue := instr. NthArgument (1);
            AssignToVar (path, instr. opndList. arg(D.Object), x)
          END;
          instr := instr. nextInstr
        END
      END
    ELSIF (path IS D.Merge) THEN
      use := path. useList;
      WHILE (use # NIL) DO
        IF (use. instr IS D.Gate) & (use. instr(D.Gate). var # NIL) THEN
          gate := use. instr(D.Gate);
          Attr.InitItem (x, S.currSymPos);
          x. currValue := gate;
          AssignToVar (path, gate. var, x)
        END;
        use := use. nextUse
      END
    ELSIF innerMost THEN
      (* innermost guard of a true/true or false/false combination; find 
         complement guard true/false or false/true *)
      IF (path. opcode = Opc.guardTrue) THEN
        searchFor := Opc.guardFalse
      ELSE
        searchFor := Opc.guardTrue
      END;
      use := path. opndList. arg. useList;
      WHILE (use. instr. opcode # searchFor) OR
            (use. instr. region # path. region) DO
        use := use. nextUse
      END;
      (* scan gates of the complementing guard `use', assign their values in
         in `path' *)
      merge := use. instr(D.Region). RegionMerge();
      opn := merge. ArgumentIndex (use. instr(D.Region))+1;
      use := merge. useList;
      WHILE (use # NIL) DO
        IF (use. instr IS D.Gate) & (use. instr(D.Gate). var # NIL) THEN
          gate := use. instr(D.Gate);
          Attr.InitItem (x, S.currSymPos);
          x. currValue := gate. NthArgument (opn);
          AssignToVar (path, gate. var, x)
        END;
        use := use. nextUse
      END
    END
  END FixupCondPath;

PROCEDURE Assertion (region: D.Region; VAR cond: Attr.Item; trap: D.Const;
                     pos: LONGINT; VAR exitInfo: Attr.ExitInfo);
  VAR                     
    merge: D.Merge;
    truePath, falsePath: D.Region;
  BEGIN
    IF StdPragmas.assertions. true THEN
      Expr.SplitIfPaths (region, cond, truePath, falsePath, merge);
      Expr.ResetVariables (merge, falsePath);
      Trap (falsePath, Opc.trapAssert, trap, StdPragmas.assertions. true, 
            pos, exitInfo);
      CommitIfMerge (merge)
    END
  END Assertion;

PROCEDURE StatementSeq* (region: D.Region; VAR exitInfo: Attr.ExitInfo);
  TYPE
    WithGuard = POINTER TO WithGuardDesc;
    WithGuardDesc = RECORD
      next: WithGuard;
      var: D.Usable;
      type: D.Struct
    END;
    
  VAR
    nestedExit: Attr.ExitInfo;
    cond: Attr.Item;
    merge: D.Merge;
    truePath, falsePath: D.Region;
    
  PROCEDURE Statement (region: D.Region; VAR exitInfo: Attr.ExitInfo);
    VAR
      x, y: Attr.Item;
      copy: D.Instruction;
      currValue: D.Usable;
      scanState: S.ScanState;

    PROCEDURE IfStatement (region: D.Region; VAR exitInfo: Attr.ExitInfo);
      VAR
        cond: Attr.Item;
        merge: D.Merge;
        truePath, falsePath: D.Region;
        nestedInfo: Attr.ExitInfo;
        pos: LONGINT;
      BEGIN  (* pre: (S.sym = S.if) OR (S.sym = S.elsif) *)
        pos := S.currSymPos;
        S.GetSym;
        Expr.Condition (region, cond, FALSE);
        S.CheckSym (S.then);
        Expr.SplitIfPaths (region, cond, truePath, falsePath, merge);
        truePath. pos := pos;
        Expr.ResetVariables (merge, truePath);
        StatementSeq (truePath, exitInfo);
        Expr.ResetVariables (merge, falsePath);
        IF (S.sym = S.elsif) OR (S.sym = S.else) THEN
          falsePath. pos := S.currSymPos;
          nestedInfo := exitInfo;
          IF (S.sym = S.elsif) THEN
            IfStatement (falsePath, nestedInfo);
          ELSE  (* (S.sym = S.else) *)
            S.GetSym;
            StatementSeq (falsePath, nestedInfo)
          END;
          Attr.ExitInfoOr (exitInfo, nestedInfo)
        END;
        CommitIfMerge (merge);
      END IfStatement;
    
    PROCEDURE RepeatStatement (region: D.Region; VAR exitInfo: Attr.ExitInfo;
                               checkForSym: SHORTINT; stepConst: LONGINT;
                               VAR condScan: S.ScanState;
                               controlVar: D.Object; endValue: Attr.Item);
      (* `checkForSym' toggles between the different syntactic variants:
            S.repeat  REPEAT statement
            S.loop    LOOP statement
            S.do      FOR statement, `stepConst', `controlVar', `endValue'
            -S.do     WHILE statement, `condScan' is postion of condition  *)
      VAR 
        cond, step: Attr.Item;
        merge, oldMerge: D.Merge;
        truePath, falsePath: D.Region;
        guardPos: LONGINT;
        endScan: S.ScanState;
        
      PROCEDURE CommitRepeatMerge (merge: D.Region; backEdge, exitEdge: D.Region; oldMerge: D.Merge);
      (* Traverses all gates in the loop's merge region and propagates them
         out of the loop, ie assigns the gates to their respective variables
         outside the loop.  The newly created gates have as operands the value
         of the variable before the loop and the value of the last assignment 
         in the loop.  *)
        VAR
          use: D.Opnd;
          gate: D.Gate;
          x: Attr.Item;
          backArg, newArg: D.Usable;
        BEGIN
          use := merge. useList;
          WHILE (use # NIL) DO
            IF (use. instr IS D.Gate) THEN
              IF (use. instr(D.Gate). var = exitInfo. exit)  THEN
                (* pseudo variable $exit: local to loop, and the gate is 
                   always FALSE *)
                use. instr. ReplaceUses (use. instr. opndList. nextOpnd. arg)
              ELSE
                gate := use. instr(D.Gate);
                backArg := gate. opndList. nextOpnd. nextOpnd. arg;

                (* assign the loop gate to the variable in the enclosing 
                   region; the procedure `AssignToVar' extracts the third 
                   operand of the  gate and takes it as the source of the 
                   assignment *)
                newArg := CorrectCondGate (exitEdge, backArg);
                gate. opndList. nextOpnd. nextOpnd. ReplaceOperand (newArg);
                Attr.InitItem (x, gate. pos);
                x. currValue := gate;
                AssignToVar (merge. region, gate. var, x);

                (* see if the last operand is a cond gate that has to be 
                   replaced by one of its operands; has to happen after the 
                   call of `AssignToVar' that expects the last gate operand to
                   be equal to the value that holds after the loop *)
                gate. opndList. nextOpnd. nextOpnd. ReplaceOperand (CorrectCondGate (backEdge, backArg));

                (* set the current value of the variable to the one that is
                   valid after the loop *)
                gate. var. currValue := newArg
              END
            END;
            use := use. nextUse
          END;
          IF (oldMerge # NIL) THEN
            oldMerge. Delete()
          END
        END CommitRepeatMerge;
      
      BEGIN
        guardPos := -1;
        (* create loop merge, insert `region' as first operand *)
        merge := D.CreateMerge (Opc.mergeLoop);
        merge. Operand (region);
        region. Insert (merge);
        merge. merge := region. merge;
        S.CheckSym (ABS (checkForSym));
        merge. pos := S.currSymPos;
        StatementSeq (merge, exitInfo);
        IF (checkForSym = S.repeat) THEN (* REPEAT statement *)
          guardPos := S.currSymPos;
          S.CheckSym (S.until);
          (* parse loop guard *)
          Expr.ConditionExit (merge, cond, exitInfo, FALSE, TRUE, FALSE, FALSE)
          
        ELSIF (checkForSym = S.loop) THEN (* LOOP statement *)
          Expr.ConditionExit (merge, cond, exitInfo,FALSE, FALSE, FALSE, FALSE)
          
        ELSIF (checkForSym = S.do) THEN  (* FOR statement *)
          Attr.InitItem (cond, S.currSymPos);
          IF (controlVar = NIL) THEN     (* faulty control variable *)
            cond. type := D.struct[D.strShortInt];
            cond. const := D.GetIntConst (1, D.struct[D.strShortInt]);
          ELSE
            cond. currValue := Expr.AccessVar (merge, controlVar);
            cond. type := controlVar. type
          END;
          Attr.InitItem (step, S.currSymPos);
          step. type := StdTypes.IntType (stepConst);
          step. const := D.GetIntConst (stepConst, step. type);
          step. currValue := step. const;
          
          (* add step constant to control variable *)
          Expr.EvalDyadicOp (merge, cond, step, Opc.classAdd, 
                             S.currSymPos, {}, {D.grpInteger+D.grpOffset});
          IF (controlVar # NIL) THEN
            AssignToVar (merge, controlVar, cond)
          END;
          
          (* compare control variable with end value *)
          IF (stepConst > 0) THEN
            Expr.EvalDyadicOp (merge, cond, endValue, Opc.classGtr,
                               S.currSymPos, {}, {D.grpInteger+D.grpOffset})
          ELSE
            Expr.EvalDyadicOp (merge, cond, endValue, Opc.classLss,
                               S.currSymPos, {}, {D.grpInteger+D.grpOffset})
          END;
          Expr.ConditionExit (merge, cond, exitInfo, FALSE, FALSE, FALSE, TRUE)
          
        ELSE                             (* WHILE statement *)
          S.SaveScanPos (endScan);
          S.RestoreScanPos (condScan);   (* move scanning position backward *)
          Expr.ConditionExit (merge, cond, exitInfo, FALSE, TRUE, TRUE, FALSE);
          S.RestoreScanPos (endScan)     (* restore scanning position *)
        END;
        
        (* split control flow into exit path and back edge, insert back edge
           as (last) operand into merge node *)
        Expr.SplitPaths (merge, cond, truePath, falsePath);
        IF (truePath. merge # NIL) & (truePath. merge = falsePath. merge) THEN
          oldMerge := truePath. merge
        ELSE
          oldMerge := NIL
        END;
        merge. Operand (falsePath);
        truePath. merge := region. merge;
        falsePath. merge := merge;
        IF (guardPos >= 0) THEN
          truePath. pos := guardPos;
          falsePath. pos := guardPos
        END;
        
        (* propagte gate values out of loop *)
        CommitRepeatMerge (merge, falsePath, truePath, oldMerge)
      END RepeatStatement;
    
    PROCEDURE WhileStatement (region: D.Region; VAR exitInfo: Attr.ExitInfo);
      VAR 
        pos: LONGINT;
        cond: Attr.Item;
        merge: D.Merge;
        truePath, falsePath: D.Region;
        condScan: S.ScanState;
      BEGIN
        pos := S.currSymPos;
        (* first parse condition as guard of an if statement *)
        S.GetSym;
        S.SaveScanPos (condScan);
        Expr.Condition (region, cond, FALSE);
        Expr.SplitIfPaths (region, cond, truePath, falsePath, merge);
        Expr.ResetVariables (merge, truePath);
        (* parse loop body, create repeat-until structure *)
        RepeatStatement (truePath, exitInfo, -S.do, 0, condScan, NIL, cond);
        (* complete if *)
        CommitIfMerge (merge);
        truePath. pos := pos;
        falsePath. pos := S.currSymPos;
        (* parse END *)
        S.CheckSym (S.end)
      END WhileStatement;

    PROCEDURE LoopStatement (region: D.Region; VAR exitInfo: Attr.ExitInfo);
      VAR
        oldExit: D.Object;
        dummy: Attr.Item;
        scanState: S.ScanState;
      BEGIN
        (* create new $exit variable, initialize to FALSE *)
        oldExit := exitInfo. exit;
        exitInfo. exit := Sym.NewObject ("$exit", D.objVar, S.currSymPos);
        exitInfo. exit. type := D.struct[D.strBoolean];
        exitInfo. exit. localTo := exitInfo. return. localTo;
        Attr.CreateItem (dummy, Sym.constFalse, S.currSymPos);
        AssignToVar (region, exitInfo. exit, dummy);
        (* create repeat loop *)
        RepeatStatement (region, exitInfo, S.loop, 0, scanState, NIL, dummy);
        IF ~(exitInfo. exited OR exitInfo. returned) THEN
          E.Err (exitInfo. exit. pos, -408) (* warning: infinite loop *)
        END;
        S.CheckSym (S.end);
        (* set `exitInfo' *)
        exitInfo. exit := oldExit;
        exitInfo. exited := FALSE
      END LoopStatement;
    
    PROCEDURE ForStatement (region: D.Region; VAR exitInfo: Attr.ExitInfo);
      VAR
        var, beg, end, cond: Attr.Item;
        step: D.Const;
        posStep, pos: LONGINT;
        merge: D.Merge;
        truePath, falsePath: D.Region;
        scanState: S.ScanState;
      BEGIN
        pos := S.currSymPos;
        S.GetSym;
        Expr.Designator (region, var);
        IF (var. obj = NIL) OR Sym.ImportedObject (Sym.mod, var. obj) THEN
          E.Err (var. basePos, 254)      (* has to be simple identifier *)
        END;
        WritableVariable (var);          (* control variable is variable *)
        S.CheckSym (S.becomes);
        Expr.Expr (region, beg);
        Expr.CheckValue (beg);
        AssignmentCompatible (region, var. type, beg);
        S.CheckSym (S.to);
        Expr.Expr (region, end);
        Expr.CheckValue (end);
        AssignmentCompatible (region, var. type, end);
        IF (S.sym = S.by) THEN
          S.GetSym;
          posStep := S.currSymPos;
          step := Expr.ConstExpr (D.grpInteger);
          IF (step. int = 0) THEN
            E.Err (posStep, 255)         (* has to be nonzero integer const *)
          ELSIF ~Sym.Includes (var. type, step. type, D.grpNumeric) THEN
            Sym.ErrT1 (posStep, 256, var. type) 
            (* too large with respect to control variable *)
          END
        ELSE
          step := D.GetIntConst (1, D.struct[D.strShortInt])
        END;
        
        (* create while loop as combination of if and repeat *)
        IF (var. obj # NIL) THEN
          AssignToVar (region, var. obj, beg);
          var. currValue := Expr.AccessVar (region, var. obj)
        END;
        cond := var;
        IF (step. int > 0) THEN
          Expr.EvalDyadicOp (region, cond, end, Opc.classLeq, 
                             beg. pos, {}, {D.grpInteger+D.grpOffset})
        ELSE
          Expr.EvalDyadicOp (region, cond, end, Opc.classGeq, 
                             beg. pos, {}, {D.grpInteger+D.grpOffset})
        END;
        Expr.SplitIfPaths (region, cond, truePath, falsePath, merge);
        truePath. pos := pos;
        Expr.ResetVariables (merge, truePath);
        (* parse loop body, create repeat-until structure *)
        RepeatStatement (truePath, exitInfo, S.do, step. int, scanState,
                         var. obj, end);
        (* complete if *)
        CommitIfMerge (merge);
        (* parse END *)
        falsePath. pos := S.currSymPos;
        S.CheckSym (S.end)
      END ForStatement;
    
    PROCEDURE CaseStatement (region: D.Region; VAR exitInfo: Attr.ExitInfo);
      VAR
        x: Attr.Item; 
        guard, else: D.Guard;
        expectedType: SHORTINT;
        nestedInfo: Attr.ExitInfo;
        
      PROCEDURE CaseLabels (guard, else: D.Guard; expectedType: SHORTINT);
        VAR
          from, to, range: D.Const;
          pos, min, max: LONGINT;
          guardOpnd, rangeOpnd: D.Opnd;
          minStr, maxStr: ARRAY 16 OF CHAR;
        
        PROCEDURE Boundary (VAR pos: LONGINT): D.Const;
          VAR
            b: D.Const;
          BEGIN
            pos := S.currSymPos;
            b := Expr.ConstExpr (expectedType);
            IF (x. type. form # D.strUndef) &
               ~(Sym.Includes (x. type, b. type, D.grpInteger) OR
                 Sym.Includes (x. type, b. type, D.grpChar)) THEN
              E.Err (pos, 261)           (* value not included in case epxr *)
            END;
            RETURN b
          END Boundary;
        
        BEGIN
          from := Boundary (pos);
          IF (S.sym = S.upto) THEN
            S.GetSym;
            to := Boundary (pos)
          ELSE
            to := from
          END;
          IF (from. int > to. int) THEN
            E.Err (pos, 236)             
            (* lower bound has to be less/equal to upper one *)
          END;
          
          (* check that range isn't used yet *)
          guardOpnd := merge. opndList. nextOpnd;
          WHILE (guardOpnd # NIL) DO
            rangeOpnd := guardOpnd. arg(D.Guard). opndList. nextOpnd;
            WHILE (rangeOpnd # NIL) DO
              range := rangeOpnd. arg(D.Const);
              min := range. int;
              IF (from. int > min) THEN
                min := from. int
              END;
              max := range. int2;
              IF (to. int < max) THEN
                max := to. int
              END;
              IF (min <= max) & (E.noerr OR (min # 1) OR (max # 1)) THEN
                (* avoid error messages caused by undefined values in the
                   label; such values are mapped to `1', which is usually
                   already used in the CASE statement *)
                IntStr.IntToStr (min, minStr);
                IntStr.IntToStr (max, maxStr);
                E.ErrIns2 (pos, 262, minStr, maxStr)
                (* case labels already used *)
              END;
              rangeOpnd := rangeOpnd. nextOpnd
            END;
            guardOpnd := guardOpnd. nextOpnd
          END;
          
          (* add range to current guard *)
          guard. Operand (D.GetRangeConst (from. int, to. int, x. type));
          
          (* remove range from else guard *)
          rangeOpnd := else. opndList. nextOpnd;
          WHILE (rangeOpnd # NIL) DO
            range := rangeOpnd. arg(D.Const);
            IF (range. int <= from. int) & (to. int <= range. int2) THEN
              rangeOpnd. DeleteOperand();
              IF (range. int < from. int) THEN
                else. Operand (D.GetRangeConst (range. int, from. int-1, x. type))
              END;
              IF (to. int < range. int2) THEN
                else. Operand (D.GetRangeConst (to. int+1, range. int2, x. type))
              END;
              rangeOpnd := NIL
            ELSE
              rangeOpnd := rangeOpnd. nextOpnd
            END
          END
        END CaseLabels;
        
      PROCEDURE AddGuard (merge: D.Merge): D.Guard;
        VAR
          guard: D.Guard;
          use: D.Opnd;
          gate: D.Gate;
        BEGIN
          guard := D.CreateGuard (x. currValue, Opc.guardCase, S.currSymPos);
          guard. opndList. pos := x. pos;
          region. Insert (guard);
          merge. Operand (guard);
          guard. merge := merge;
          (* extend existing gates by one operand *)
          use := merge. useList;
          WHILE (use # NIL) DO
            IF (use. instr IS D.Gate) THEN
              gate := use. instr(D.Gate);
              gate. Operand (gate. oldValue)
            END;
            use := use. nextUse
          END;
          RETURN guard
        END AddGuard;
      
      BEGIN
        exitInfo. exited := FALSE;
        exitInfo. returned := FALSE;
        exitInfo. trapped := FALSE;
        nestedInfo := exitInfo;
        
        S.GetSym;
        Expr.Expr (region, x);
        Expr.CheckValue (x);
        expectedType := D.grpInteger;
        IF Sym.TypeInGroup (x. type, D.grpChar) THEN
          expectedType := D.grpChar
        ELSIF ~Sym.TypeInGroup (x. type, D.grpInteger) THEN
          E.Err (x. pos, 260)            
          (* integer or char expression expected *)
        END;
        S.CheckSym (S.of);
        merge := D.CreateMerge (Opc.mergeCase);
        region. Insert (merge);
        else := AddGuard (merge);
        (* add full range to else guard *)
        else. Operand (D.GetRangeConst (
          StdTypes.WholeMin (D.OperatorSubclass (x. type, 0)),
          StdTypes.WholeMax (D.OperatorSubclass (x. type, 0)), x. type));
        
        LOOP
          IF (S.sym < S.bar) THEN
            guard := AddGuard (merge);
            CaseLabels (guard, else, expectedType);
            WHILE (S.sym = S.comma) DO
              S.GetSym;
              CaseLabels (guard, else, expectedType)
            END;
            S.CheckSym (S.colon);
            D.SortRanges (guard);
            StatementSeq (guard, nestedInfo);
            Attr.ExitInfoOr (exitInfo, nestedInfo);
            Expr.ResetVariables (merge, NIL)
          END;
          IF (S.sym # S.bar) THEN
            EXIT
          END;
          S.GetSym
        END;
        D.SortRanges (else);
        
        else. pos := S.currSymPos;
        IF (S.sym = S.else) THEN
          S.GetSym;
          StatementSeq (else, nestedInfo);
          Attr.ExitInfoOr (exitInfo, nestedInfo)
        ELSE
          Trap (else, Opc.trapCase, x. currValue, StdPragmas.caseSelectCheck. true, 
                x. pos, exitInfo)
        END;
        S.CheckSym (S.end);
        CommitIfMerge (merge)
      END CaseStatement;
    
    PROCEDURE WithStatement (region: D.Region; guardList: WithGuard;
                             VAR exitInfo: Attr.ExitInfo);
      VAR
        cond: Attr.Item;
        merge: D.Merge;
        truePath, falsePath: D.Region;
        nestedInfo: Attr.ExitInfo;
        newGuard, guard: WithGuard;
        var, type: Attr.Item;
        oldType: D.Struct;
        ok, oldTwistedFlag: BOOLEAN;
        
      PROCEDURE Guard (VAR cond: Attr.Item);
        BEGIN
          Expr.Designator (region, var);
          ok := FALSE;
          IF (var. obj = NIL) THEN
            E.Err (var. basePos, 263)    (* has to be (qualified) ident *)
          ELSE
            ok := TRUE
          END;
          S.CheckSym (S.colon);
          Expr.Designator (region, type);
          IF (type. obj = NIL) OR (type. obj. mode # D.objType) THEN
            E.Err (type. pos, 211);      (* no data type *)
            ok := FALSE
          ELSE
            guard := guardList;
            WHILE (guard # NIL) &
                  ((var. currValue # guard. var) OR 
                   ~Sym.ExtensionOf (type. type, guard. type)) DO
              guard := guard. next
            END;
            IF (guard # NIL) THEN
              E.Err (type. pos, -412)    (* guard never reached *)
            END
          END;
          Expr.TypeTest (region, var, type, FALSE, type. pos, cond);
          
          (* add current guard to list *)
          NEW (newGuard);
          newGuard. next := guardList;
          newGuard. var := var. currValue;
          newGuard. type := type. type
        END Guard;
  
      BEGIN  (* pre: (S.sym = S.with) OR (S.sym = S.bar) *)
        S.GetSym;
        Guard (cond);
        S.CheckSym (S.do);
        Expr.SplitIfPaths (region, cond, truePath, falsePath, merge);
        
        IF ok THEN
          oldType := var. type;
          oldTwistedFlag := (D.objIsTwisted IN var. obj. flags);
          var. obj. type := type. type;  (* modify symbol table *)
          INCL (var. obj. flags, D.objIsTwisted);
          ASSERT (var. obj. localDecl = NIL);  (* ... *)
          IF (D.objIsParameter IN var. obj. flags) &
             ~StdPragmas.conformantMode. true THEN
            (* the formal paramter's type was changed, but this shouldn't have
               any effect on the _outer_ appearance of the procedure in non-
               conformant mode; place a hint designating the original type in 
               the parameter object; it'll be evaluated by Sym.ParameterType *)
            var. obj. localDecl := Sym.FindDecl (Sym.currScope, var.obj.name^);
            ASSERT (var. obj. localDecl # NIL)  (* ... *)
          END;
          StatementSeq (truePath, exitInfo);
          var. obj. type := oldType;     (* cleanup symbol table *)
          var. obj. localDecl := NIL;
          IF ~oldTwistedFlag THEN
            EXCL (var. obj. flags, D.objIsTwisted)
          END
        ELSE
          StatementSeq (truePath, exitInfo)
        END;
        
        Expr.ResetVariables (merge, NIL);
        nestedInfo := exitInfo;
        IF (S.sym = S.bar) OR (S.sym = S.else) THEN
          IF (S.sym = S.bar) THEN
            WithStatement (falsePath, newGuard, nestedInfo)
          ELSE  (* (S.sym = S.else) *)
            S.GetSym;
            StatementSeq (falsePath, nestedInfo)
          END;
        ELSE  (* here should follow an END symbol *)
          Trap (falsePath, Opc.trapWith, NIL, StdPragmas.typeGuard. true, 
                S.currSymPos, nestedInfo)
        END;
        Attr.ExitInfoOr (exitInfo, nestedInfo);
        CommitIfMerge (merge)
      END WithStatement;
    
    PROCEDURE TypeAssertion (VAR var: Attr.Item): D.Usable;
      VAR
        instr: D.Instruction;
        type: Attr.Item;
      BEGIN
        IF E.noerr & (var. ttHint # NIL) THEN  (* variable has dynamic type *)
          instr := region. CreateInstruction (Opc.typeAssert, var. type, var. pos);
          INCL (instr. flags, D.instrNotDead);
          IF StdPragmas.typeGuard. true THEN
            Attr.ContainsRuntimeCheck (region)
          ELSE
            INCL (instr. flags, D.instrIsDisabled)
          END;
          Attr.Operand (instr, var);
          instr. Operand (Attr.TypeTag (region, var, -1));
          Attr.CreateItem (type, var. type, var. pos);
          instr. Operand (Attr.TypeTag (region, type, 0));
          RETURN instr
        ELSE
          RETURN x. currValue
        END
      END TypeAssertion;
    
    PROCEDURE StructCopy (region: D.Region; currValue: D.Usable; 
                          VAR x, y: Attr.Item);
      VAR
        instr: D.Instruction;
      BEGIN
        instr := region. CreateInstruction (Opc.structCopy, x. type, x. pos);
        instr. Operand (currValue);
        instr. opndList. pos := y. pos;
        instr. Operand (Attr.Adr (region, x));
        IF Sym.TypeInGroup (y. type, D.grpStringConst) THEN
          instr. Operand (D.GetIntConst ((y. const. int+1)*
            D.struct[y. type. form+(D.strChar8-D.strStringConst8)]. size,
            D.struct[D.strLongInt]))
        ELSE
          instr. Operand (D.GetIntConst (x. type. size, 
                                           D.struct[D.strLongInt]))
        END;
        Attr.Operand (instr, y);
        instr. Operand (Attr.Adr (region, y));
        Attr.CreateItem (y, instr, x. pos)
      END StructCopy;
    
    PROCEDURE DisabledAssert (region: D.Region; proc: Attr.Item; 
                              VAR result: Attr.Item; 
                              VAR exitInfo: Attr.ExitInfo);
      VAR
        cond: Attr.Item;
        merge: D.Merge;
        truePath, falsePath: D.Region;
      BEGIN
        Attr.CreateItem (cond, Sym.constFalse, x. pos);
        Expr.SplitIfPaths (region, cond, truePath, falsePath, merge);
        Expr.ResetVariables (merge, truePath);
        ProcedureCall (truePath, x, x, exitInfo, TRUE);
        CommitIfMerge (merge)
      END DisabledAssert;
       
    BEGIN
      exitInfo. returned := FALSE;
      exitInfo. exited := FALSE;
      exitInfo. trapped := FALSE;
      IF (S.sym = S.ident) THEN
        Expr.Designator (region, x);
        IF ((S.sym = S.becomes) OR (S.sym = S.eql) OR (S.sym = S.colon)) &
           ((x. obj = NIL) OR (x. obj. mode # D.objTBProc)) THEN
          S.CheckSym (S.becomes);
          copy := Expr.InsertTempCopy (region, x);
          Expr.Expr (region, y);
          Expr.QueryTempCopy (x, copy, 1);
          Expr.RedoDesignatorAccess (region, x);
          AssignmentCompatible (region, x. type, y);
          WritableVariable (x);
          
          IF Sym.TypeInGroup (x. type, D.grpStructured) THEN
            IF (x. type. form = D.strRecord) THEN
              (* assert that dynamic type of `x' equals its static one *)
              currValue := TypeAssertion (x)
            ELSE
              currValue := x. currValue
            END;
            
            (* assigning a structured variable; add an instruction to do the
               memory copy *)
            StructCopy (region, currValue, x, y)
          END;
          
          AssignToDesignator (region, x, y)  
        ELSE                             (* procedure call *)
          IF (x. type. form = D.strProc) & (x. obj # NIL) &
             (x. obj. data # NIL) & (x. obj. data IS D.Const) &
             (x. obj. data(D.Const). int = Sym.predASSERT) &
             ~StdPragmas.assertions. true THEN
            (* this hack implements the switch to disable ASSERT code; if 
               asserts are disabled they are turned into this kind of code:
               "IF FALSE THEN ASSERT(..) END"; unreachable code elimination
               will rid us of the unused GSA code later on *)
            DisabledAssert (region, x, x, exitInfo)
          ELSE
            ProcedureCall (region, x, x, exitInfo, TRUE)
          END
        END
      ELSIF (S.sym = S.if) THEN          (* IF statement *)
        IfStatement (region, exitInfo);
        S.CheckSym (S.end)
      ELSIF (S.sym = S.case) THEN        (* CASE statement *)
        CaseStatement (region, exitInfo)
      ELSIF (S.sym = S.while) THEN       (* WHILE statement *)
        WhileStatement (region, exitInfo)
      ELSIF (S.sym = S.repeat) THEN      (* REPEAT statement *)
        RepeatStatement (region, exitInfo, S.repeat, 0, scanState, NIL, cond)
      ELSIF (S.sym = S.for) THEN         (* FOR statement *)
        ForStatement (region, exitInfo)
      ELSIF (S.sym = S.loop) THEN        (* LOOP statement *)
        LoopStatement (region, exitInfo)
      ELSIF (S.sym = S.with) THEN        (* WITH statement *)
        WithStatement (region, NIL, exitInfo);
        S.CheckSym (S.end)
      ELSIF (S.sym = S.exit) THEN        (* EXIT statement *)
        IF (exitInfo. exit = NIL) THEN
          E.Err (S.currSymPos, 242)      (* EXIT not within a LOOP *)
        ELSE
          Attr.InitItem (x, S.currSymPos);
          x. type := D.struct[D.strBoolean];
          x. currValue := Sym.constTrue;
          AssignToVar (region, exitInfo. exit, x);
          exitInfo. exited := TRUE
        END;
        S.GetSym
      ELSIF (S.sym = S.return) THEN      (* RETURN statement *)
        S.GetSym;
        AssignBoolean (region, exitInfo. return, TRUE);
        exitInfo. returned := TRUE;
        IF (S.sym < S.semicolon) THEN
          IF (exitInfo. result = NIL) THEN
            E.Err (S.currSymPos, 240)    (* not a function procedure *)
          END;
          Expr.Expr (region, x);
          Expr.CheckValue (x);
          IF (exitInfo. result # NIL) THEN
            AssignmentCompatible (region, exitInfo. result. type, x);
            AssignToVar (region, exitInfo. result, x)
          END
        ELSIF (exitInfo. result # NIL) THEN
          E.Err (S.lastSymEnd, 241);     (* missing function result *)
          AssignBoolean (region, exitInfo. result, FALSE)
        END
      END
    END Statement;

  PROCEDURE StatementSep (sym: INTEGER): BOOLEAN;
    BEGIN
      IF (sym = S.semicolon) THEN
        RETURN TRUE
      ELSIF (S.end <= sym) & (sym <= S.until) OR 
            (sym = S.bar) OR (sym = S.endOfFile) THEN
        RETURN FALSE
      ELSE
        S.CheckSym (S.semicolon);
        RETURN TRUE
      END
    END StatementSep;
  
  BEGIN
    Statement (region, exitInfo);
    WHILE StatementSep (S.sym) & 
          ~(exitInfo. returned OR exitInfo. exited OR exitInfo. trapped) DO
      IF (S.sym # S.ident) & ((S.sym < S.if) OR (S.sym > S.return)) THEN
        S.GetSym
      END;
      Statement (region, exitInfo)
    END;
    IF StatementSep (S.sym) THEN
      IF (S.sym # S.ident) & ((S.sym < S.if) OR (S.sym > S.return)) THEN
        S.GetSym
      END;
      (* previous statement set $return, $exit, or $trap: guard the following 
         statements against it *)
      Expr.ConditionExit (region, cond, exitInfo, TRUE, FALSE, FALSE, FALSE);
      Expr.SplitIfPaths (region, cond, truePath, falsePath, merge);
      nestedExit := exitInfo;
      StatementSeq (truePath, nestedExit);
      CommitIfMerge (merge);
      Attr.ExitInfoOr (exitInfo, nestedExit)
    END
  END StatementSeq;

BEGIN
  Expr.ProcedureCall := ProcedureCall;
  Expr.CommitIfMerge := CommitIfMerge;
  Expr.FixupCondPath := FixupCondPath;
  Expr.AssignToVar := AssignToVar;
  Expr.ReclaimFromMem := ReclaimFromMem;
  setAssignHints := FALSE
END ParseStatm.
