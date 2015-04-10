(* 	$Id: ParseExpr.Mod,v 1.121 2000/12/27 16:32:19 ooc-devel Exp $	 *)
MODULE ParseExpr;
(*  Parses Oberon-2 expressions and translates them to GSA.
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
  Strings, E := Error, S := Scanner, D := Data, StdTypes, StdPragmas,
  Sym := SymbolTable, Opc := Opcode, Int := IntArith,
  Const := ConstPropagation, Attr := Attributes;

     
VAR 
  receiverDesignator-: Attr.Item;
  (* set by `Designator' to hold the receiver of a type-bound procedure's
     designator; only valid after `Designator' if this procedure returns a
     type-bound procedure designator *)
     
  ProcedureCall*: PROCEDURE (region: D.Region; proc: Attr.Item; 
                             VAR result: Attr.Item; 
                             VAR exitInfo: Attr.ExitInfo; statement: BOOLEAN);
  CommitIfMerge*: PROCEDURE (region: D.Region);
  FixupCondPath*: PROCEDURE (path: D.Region; oldMerge: D.Merge; 
                             merge: D.Merge; innerMost: BOOLEAN);
  AssignToVar*: PROCEDURE (region: D.Region; dest: D.Object; VAR x: Attr.Item);
  ReclaimFromMem*: PROCEDURE (instr: D.Instruction);
  (* the above variables correspond to procedures defined in `ParseStatm' *)



PROCEDURE Dominates* (reg0, reg1: D.Region): BOOLEAN;
(* TRUE iff region `reg0' dominates region `reg1', ie, if every path from the 
   top-most region greg to `reg1' includes `reg0'.  *)
  BEGIN
    WHILE (reg1 # NIL) & (reg0 # reg1) DO
      reg1 := reg1. region
    END;
    RETURN (reg1 # NIL)
  END Dominates;

PROCEDURE GuardClass* (i: D.Instruction): INTEGER;
(* If `i' is a merge instruction, then result is `Opc.guardTrue' if `i' 
   combines two true paths, `Opc.guardFalse' if `i' combines two false paths,
   and -1 otherwise.  *)
  VAR
    left, right: INTEGER;
  BEGIN
    CASE i. opcode OF
    | Opc.guardTrue: RETURN Opc.guardTrue
    | Opc.guardFalse: RETURN Opc.guardFalse
    | Opc.mergeCond:
      left := GuardClass (i. opndList. arg(D.Instruction));
      right := GuardClass (i. opndList. nextOpnd. arg(D.Instruction));
      IF (left = right) THEN
        RETURN left
      ELSE
        RETURN -1
      END
    END
  END GuardClass;

PROCEDURE ResetVariables* (merge: D.Region; usePath: D.Region);
(* Sets the `currValue' entries of variables associated with gates in `merge'.
   If `usePath=NIL', then the gates `oldValue' entries are used for that
   purpose, otherwise the gate operand that is associated with `usePath'.  In 
   the latter case `usePath' has to be one of the operands of `merge', ie a 
   path leading into `merge'.  *)
  VAR
    use: D.Opnd;
    gate: D.Gate;
    opn: INTEGER;
  BEGIN
    IF (usePath = NIL) THEN
      use := merge. useList;
      WHILE (use # NIL) DO
        IF (use. instr IS D.Gate) THEN
          gate := use. instr(D.Gate);
          gate. var. currValue := gate. oldValue
        END;
        use := use. nextUse
      END
    ELSE
      opn := merge. ArgumentIndex (usePath)+1;
      use := merge. useList;
      WHILE (use # NIL) DO
        IF (use. instr IS D.Gate) THEN
          gate := use. instr(D.Gate);
          IF (gate. var # NIL) THEN
            gate. var. currValue := gate. NthArgument (opn)
          END
        END;
        use := use. nextUse
      END
    END
  END ResetVariables;


PROCEDURE AddStructToEnter* (region: D.Region; struct: D.Struct);
  VAR
    enter: D.Instruction;
  BEGIN
    IF (struct. currValue = struct) THEN
      (* add type as result to the enter instruction and take the result as 
         its value *)
      enter := region. EnterInstr();
      struct. currValue := enter. AppendResult (D.CreateSymLocation (struct, D.symLocObject), NIL)
    END
  END AddStructToEnter;

PROCEDURE DegenerateValueParam (obj: D.Object): BOOLEAN;
(* TRUE iff `obj' is value parameter of type open array, but without any
   length information *)
  BEGIN
    RETURN (obj. mode = D.objVar) &
           (obj. type. form = D.strOpenArray) &
           (D.objIsParameter IN obj. flags) &
           (D.objNoLengthTag IN obj. flags)
  END DegenerateValueParam;

PROCEDURE AccessVar* (region: D.Region; var: D.Object): D.Usable;
  VAR
    enter, instr: D.Instruction;
    res: D.Result;
  BEGIN
    IF (var. currValue = var) &
       ((var. mode = D.objVarPar) OR (var = Sym.mem)) THEN
      (* accessing nonlocal object with undefined current value: add it as 
         result to the enter instruction and take the result as its value;
         accesses to nonlocal variables aren't handled here *)
      enter := region. EnterInstr();
      var. currValue := enter. AppendResult (D.CreateSymLocation (var, D.symLocObject), var. type)
    END;
    
    IF (var = Sym.mem) THEN
      (* take current value from variable $mem *)
      
    ELSIF (var. mode = D.objVarPar) OR DegenerateValueParam (var) THEN
      instr := region. CreateInstruction (Opc.accessVarParam, var. type, S.currSymPos);
      instr. Operand (var);
      instr. Operand (Attr.Address (region, var, S.currSymPos));
      instr. Operand (Sym.store. currValue);
      var. currValue := instr
      
    ELSIF (var. localTo # Sym.currScope) OR (var. level = Sym.globalLevel) THEN
      (* within the module body, global variables of the own module are
         treated as non-local, because they are visibile to all procedures
         of the module and can also be modified by them *)
      IF Attr.TracesToEmptyStore (var, Sym.store. currValue) THEN
        (* add nonlocal object to enter instruction *)
        res := Attr.FindAddEnterResult (region, var, D.symLocObject,
                                        var. type)
      END;
      instr := region. CreateInstruction (Opc.accessNonlocal, var. type, S.currSymPos);
      instr. Operand (var);
      instr. Operand (Attr.Address (region, var, S.currSymPos));
      instr. Operand (Sym.store. currValue);
      var. currValue := instr
    END;
    RETURN var. currValue
  END AccessVar;

PROCEDURE RedoDesignatorAccess* (region: D.Region; VAR x: Attr.Item);
(* If the value of `x' has changed since it was parsed originally, redo the
   whole access procedure and put the new value into `x'.
   pre: `x' is a variable designator (not constant, nor expression).  *)
     
  PROCEDURE DuplicateAccessChain (value: D.Usable): D.Usable;
  (* Inspect the sequence of access instructions in `value' and create code
     to do the same sequence again.  Return the top level access and update
     `baseValue' to the replaced variable access.  *)
    VAR
      instr, guard, access: D.Instruction;
      new: D.Usable;
      opnd: D.Opnd;
      memAssign: Attr.Item;
    
    PROCEDURE CopyOpndPos (from, to: D.Instruction);
      VAR
        o1, o2: D.Opnd;
      BEGIN
        o1 := from. opndList; o2 := to. opndList;
        WHILE (o1 # NIL) DO
          o2. pos := o1. pos; o1 := o1. nextOpnd; o2 := o2. nextOpnd
        END;
        ASSERT (o1 = o2)
      END CopyOpndPos;
    
    BEGIN
      IF (value = x. baseValue) THEN  (* variable or heap access *)
        IF (x. assignment IS D.Struct) THEN
          access := value(D.Instruction);
          instr := region. CreateInstruction (Opc.accessHeap, x. assignment(D.Struct), access. pos);
          instr. flags := access. flags; access. flags := {};
          instr. Operand (x. assignment);
          instr. Operand (access. opndList. nextOpnd. arg);
          instr. Operand (AccessVar (region, Sym.store));
          CopyOpndPos (access, instr);
          x. baseValue := instr
        ELSE
          x. baseValue := AccessVar (region, x. assignment(D.Object))
        END;
        RETURN x. baseValue
      
      ELSIF (value(D.Instruction). opcode = Opc.typeGuard) OR
            (value(D.Instruction). opcode = Opc.typeAssert) THEN
        guard := value(D.Instruction);
        new := DuplicateAccessChain (guard. opndList. arg);
        instr := region. CreateInstruction (guard. opcode, guard. type, guard. pos);
        instr. flags := guard. flags; guard. flags := {};
        instr. Operand (new);
        opnd := guard. opndList. nextOpnd;
        WHILE (opnd # NIL) DO
          instr. Operand (opnd. arg);
          opnd := opnd. nextOpnd
        END;
        CopyOpndPos (guard, instr);
        RETURN instr
        
      ELSIF (value(D.Instruction). opcode = Opc.accessMem) THEN
        (* access to a volatile variable, encoded as direct memory access;
           problem: the previous instruction writes to $mem, this must be
           undone *)
        access := value(D.Instruction);
        instr := region. CreateInstruction (Opc.accessMem, access. type, access. pos);
        instr. flags := access. flags; access. flags := {};
        instr. Operand (access. opndList. arg);
        instr. Operand (AccessVar (region, Sym.mem));
        instr. SetOpndSymLoc (Sym.mem);
        instr. Operand (AccessVar (region, Sym.store));
        instr. SetOpndSymLoc (Sym.store);
        Attr.CreateItem (memAssign, instr. AppendResult (D.CreateSymLocation (Sym.mem, D.symLocObject), NIL), x. pos);
        AssignToVar (region, Sym.mem, memAssign);
        ReclaimFromMem (instr);
        CopyOpndPos (access, instr);

        access. nextResult. ReplaceUses (access. opndList. nextOpnd. arg);
        access. nextResult. nextResult. ReplaceUses (access. opndList. nextOpnd. nextOpnd. arg);
        access. Delete;
        RETURN instr
        
      ELSE  (* field or element access *)
        access := value(D.Instruction);
        new := DuplicateAccessChain (access. opndList. arg);
        instr := region. CreateInstruction (access. opcode, access. type, access. pos);
        instr. flags := access. flags; access. flags := {};
        instr. Operand (new);
        instr. Operand (access. NthArgument (1));
        instr. Operand (access. NthArgument (2));
        CopyOpndPos (access, instr);
        RETURN instr
      END
    END DuplicateAccessChain;
  
  PROCEDURE SideEffected (VAR x: Attr.Item): BOOLEAN;
  (* Result is TRUE iff the value of designator `x' may have changed since it
     was first determined.  *)
    VAR
      instr: D.Instruction;
      obj: D.Object;
    BEGIN
      IF (x. assignment = NIL) THEN
        RETURN FALSE
      ELSIF (x. assignment IS D.Struct) THEN
        instr := x. baseValue(D.Instruction);
        RETURN (instr. NthArgument (2) # Sym.store. currValue)
      ELSE  (* (x. assignment IS D.Object) *)
        obj := x. assignment(D.Object);
        IF (obj. mode = D.objVarPar) OR (obj. localTo # Sym.currScope) THEN
          instr := x. baseValue(D.Instruction);
          RETURN (instr. NthArgument (2) # Sym.store. currValue)
        ELSE
          RETURN (x. baseValue # obj. currValue)
        END
      END
    END SideEffected;
  
  BEGIN
    IF SideEffected (x) THEN
      x. currValue := DuplicateAccessChain (x. currValue)
    END
  END RedoDesignatorAccess;



PROCEDURE CheckType (type: D.Struct; expected: SHORTINT; pos: LONGINT);
(* Emit an error if `type' doesn't match the one described by `expected'.  *)
  VAR
    ins: ARRAY 256 OF CHAR;
    class: ARRAY 16 OF CHAR;
  BEGIN
    IF (type. form # D.strUndef) & ~Sym.TypeInGroup (type, expected) THEN
      CASE ABS (expected) OF
      | D.strBoolean: class := "Boolean"
      | D.grpInteger: class := "Integer"
      | D.grpSet    : class := "Set"
      END;
      Sym.TypeName (ins, type);
      E.ErrIns2 (pos, 234, class, ins)
    END
  END CheckType;

PROCEDURE Qualident* (VAR x: Attr.Item);
(* Reads a (possibly quailified) identifier at the current position in the
   token stream.
   post: `x. obj' contains the denoted (possibly imported) object, `x. pos' the
     current position in the source code. If the current token is not an
     identifier or no declared object, `x. obj' is set to a variable with the
     type `Sym.struct[strUndef]'.  *)
  BEGIN
    Attr.InitItem (x, S.currSymPos);
    IF (S.sym = S.ident) THEN  (* identifier, search current scope for it *)
      x. obj := Sym.Find (S.str^);
      S.GetSym;
      (* if no declaration of that name exists and '.' follows, skip two
         tokens (period+ident) *)
      IF (x. obj = NIL) & (S.sym = S.period) THEN
        S.GetSym;  (* skip period *)
        S.GetSym   (* probably identifier, skip it *)
      END
    ELSE  (* no identifier, syntax error *)
      x. obj := NIL
    END;
    IF (x. obj # NIL) THEN  (* a declaration with this name exists *)
      IF (x. obj. mode=D.objType) & (D.objIsForwardDecl IN x. obj. flags) THEN
        x. obj := NIL  (* forward declared types officially don't exist *)
      ELSIF (x. obj. mode = D.objModule) THEN
        (* we got a module here, read the imported object *)
        
        (* enable underscore for identifiers if allowed by imported module *)
        S.allowUnderscore := (D.objAllowsUnderscore IN x. obj. flags);
        
        S.CheckSym (S.period);
        IF (S.sym = S.ident) THEN
          (* search for the identifier in the module's scope *)
          x. pos := S.currSymPos;
          x. obj := Sym.FindDecl (x. obj, S.str^);
          IF (x. obj # NIL) & ~Sym.Visible (Sym.currScope, x. obj) THEN
            (* if the identifier is not exported, ignore the entry *)
            x. obj := NIL
          END;
          S.allowUnderscore := (D.objAllowsUnderscore IN Sym.mod. flags);
          S.GetSym
        ELSE
          x. obj := NIL
        END
      ELSIF (D.objIsParameter IN x. obj. flags) THEN
        (* instead of using the parameter object that is part of the scope,
           return the parameter that is part of the formal parameter list; this
           resolves the duplicity of having two copies of each parameter 
           around: we simply choose to use only one of them *)
        x. obj := x. obj. data(D.Object)
      END
    END;
    
    IF (x. obj = NIL) THEN
      (* no legal object found: give error message and fill `obj' with a dummy
         variable *)
      E.Err (x. pos, 197);               (* undeclared identifier *)
      x. obj := Sym.NewObject (S.undefStr, D.objVar, x. pos);
      x. obj. localTo := Sym.currScope;
      x. obj. type := D.struct[D.strUndef]
    ELSIF (x. obj. localTo # Sym.currScope) THEN
      (* object is accessed from nested scope *)
      INCL (x. obj. flags, D.objIsUsedNonlocal)
    END
  END Qualident;

PROCEDURE TypeQualident* (VAR type: D.Struct; VAR pos: LONGINT);
(* Reads qualified identifier that has to denote a type, otherwise an error is
   signaled.
   post: `type # NIL' *)
  VAR
    x: Attr.Item;
  BEGIN
    Qualident (x);
    pos := x. pos;
    IF (x. obj. mode # D.objType) THEN
      E.Err (pos, 211);                  (* no data type *)
      type := D.struct[D.strUndef]
    ELSE
      type := x. obj. type
    END
  END TypeQualident;

PROCEDURE TypeTest* (region: D.Region; var, type: Attr.Item; 
                     guard: BOOLEAN; pos: LONGINT; VAR result: Attr.Item);
(* Creates type test (`guard=FALSE') or type guard (`guard=TRUE').  *)
  VAR
    instr, access: D.Instruction;
    t: D.Struct;
    
  PROCEDURE HasDynamicType (VAR x: Attr.Item): BOOLEAN;
  (* Result is TRUE iff `x' has a dynamic type that may differ from the static
     one, ie if `x' is a record pointer or a variable record parameter.  
     Otherwise a more or less useful error message is emitted.  *)
    BEGIN
      IF (x. type. form = D.strUndef) THEN
        (* don't barf, the designator was faulty anyway *)
        RETURN TRUE
      ELSIF (x. type. form = D.strPointer) THEN
        IF (x. type. base. form = D.strRecord) THEN
          RETURN TRUE
        ELSE
          E.Err (x. pos, 258)              (* not a record pointer *)
        END
      ELSIF (x. type. form = D.strRecord) THEN
        IF (x. ttHint # NIL) THEN
          (* a type tag is present if `x' is a variable parameter, or if it is
             a dereferenced record pointer; ParseExpr.Designator sets the field
             `ttHint' accordingly *)
          RETURN TRUE
        ELSE
          E.Err (x. pos, 257)            (* var has no dynamic type *)
        END                  
      ELSE
        E.Err (x. pos, 257)              (* var has no dynamic type *)
      END;
      RETURN FALSE
    END HasDynamicType;
  
  PROCEDURE BaseTypes (t: D.Struct): INTEGER;
    BEGIN
      IF (t. form = D.strPointer) THEN
        t := t. base
      END;
      IF (t. base = NIL) THEN
        RETURN 0
      ELSE
        RETURN BaseTypes (t. base)+1
      END
    END BaseTypes;
  
  BEGIN
    IF HasDynamicType (var) THEN
      IF Sym.ExtensionOf (type. type, var. type) THEN
        IF Sym.SameType (type. type, var. type) THEN
          IF guard THEN
            E.Err (type. pos, -409)      (* warning: redundant type guard *)
          ELSE
            E.Err (type. pos, -410)      (* warning: type test is always TRUE*)
          END
        END;
        
        access := NIL;
        IF guard THEN
          instr := region. CreateInstruction (Opc.typeGuard, type.type, pos);
          INCL (instr. flags, D.instrNotDead);
          IF StdPragmas.typeGuard. true THEN
            Attr.ContainsRuntimeCheck (region)
          ELSE
            INCL (instr. flags, D.instrIsDisabled)
          END;
          
          (* a type guard like "p^(R)" needs to be be turned into the 
             equivalent designator "p(POINTER TO R)^" to avoid a messed up 
             access and update history for the heap *)
          IF (var. currValue IS D.Instruction) &
             (var. currValue(D.Instruction). opcode = Opc.accessHeap) THEN
            access := var. currValue(D.Instruction);
            t := type. type;
            IF (t. form = D.strPointer) THEN
              t := t. base
            END;
            access. opndList. ReplaceOperand (t)
          END
        ELSE
          instr := region. CreateInstruction (Opc.typeTest, D.struct[D.strBoolean], pos)
        END;
        IF (access # NIL) THEN
          instr. Operand (access. opndList. nextOpnd. arg)
        ELSE
          Attr.Operand (instr, var)
        END;
        instr. Operand (Attr.TypeTag (region, var, -1));
        instr. Operand (Attr.TypeTag (region, type, 0));
        instr. Operand (D.GetIntConst (BaseTypes (type. type), 
                                         D.struct[D.strInteger]));
        IF (access # NIL) THEN
          access. opndList. nextOpnd. ReplaceOperand (instr);
          Attr.CreateItem (result, access, pos)
        ELSE
          Attr.CreateItem (result, instr, pos)
        END;
        RETURN
      ELSE
        Sym.ErrT1 (type. pos, 259, var. type) (* type not extension of var *)
      END
    END;
    IF guard THEN
      result := var
    ELSE
      Attr.CreateItem (result, Sym.constFalse, pos)
    END
  END TypeTest;



PROCEDURE ^ Expr* (region: D.Region; VAR x: Attr.Item);

PROCEDURE EvalInstr* (VAR x: Attr.Item; instr: D.Instruction);
(* Looks, if possible, for errors in `instr' and tries to apply constant 
   folding on it.  If folding is possible then `instr' is deleted (ie it 
   shouldn't be used).  The fields `type', `const', and `currValue' of `x' are
   set accordingly.  *)
  VAR
    class, subclass: SHORTINT;
    const: D.Const;
  BEGIN
    class := SHORT (instr. opcode DIV Opc.sizeClass);
    IF ((class = Opc.classDivInt) OR (class = Opc.classMod)) &
       StdPragmas.intDivCheck. true THEN
      instr. flags := instr. flags+{D.instrCheckDiv, D.instrNotDead};
      Attr.ContainsRuntimeCheck (instr. region)
    ELSIF (class = Opc.classDivReal) & StdPragmas.intDivCheck. true THEN
      instr. flags := instr. flags+{D.instrCheckDiv, D.instrNotDead};
      Attr.ContainsRuntimeCheck (instr. region)
    ELSIF ((Opc.classAdd <= class) & (class <= Opc.classNeg) OR
        (class = Opc.classAbs) OR (class = Opc.classAsh)) THEN
      subclass := SHORT (instr. opcode MOD Opc.sizeClass);
      IF ((subclass < Opc.subclR) & StdPragmas.intOverflowCheck. true) OR
         ((subclass >= Opc.subclR) & StdPragmas.realOverflowCheck. true) THEN
        instr. flags := instr.flags + {D.instrNotDead, D.instrCheckOverflow};
        Attr.ContainsRuntimeCheck (instr. region)
      END
    END;
    const := Const.TryConstantFolding (instr, TRUE);
    IF (const = NIL) THEN
      Const.CheckConstSemantics (instr);
      Attr.CreateItem (x, instr, instr. pos)
    ELSE
      Attr.CreateItem (x, const, instr. pos);
      (* remove `mayTrap' flag from folded instruction in order to make dead 
         code elimination remove `instr' *)
      EXCL (instr. flags, D.instrNotDead)
    END
  END EvalInstr;

PROCEDURE TypeConversion* (region: D.Region; VAR x: Attr.Item; 
                           targetType: SHORTINT; adaptType: BOOLEAN;
                           pos: LONGINT);
  VAR
    src, dst, oldSrc, oldDst: SHORTINT;
    err: INTEGER;
    arg: D.Usable;
    instr: D.Instruction;
    lreal: LONGREAL;
    c: D.Const;
    
  PROCEDURE GetIntConst (value: LONGINT): D.Const;
  (* if `adaptType', then get smallest integer type which can
     hold the value `value', type of `targetType' otherwise. *)
    BEGIN
      IF adaptType &
         (D.strShortInt <= targetType) & (targetType <= D.strHugeInt) THEN
        RETURN D.GetIntConst (value, StdTypes.IntType (value))
      ELSE
        RETURN D.GetIntConst (value, D.struct[targetType])
      END
    END GetIntConst;
  
  BEGIN
    IF (x. type. form # targetType) THEN
      src := D.OperatorSubclass (x. type, 0);
      dst := D.OperatorSubclass (NIL, targetType);
      IF (x. const # NIL) THEN           (* conversion of constant *)
        IF (D.strSet8 <= targetType) & (targetType <= D.strSet64) THEN
          x. const := D.GetSetConst (x. const. set, D.struct[targetType])
        ELSIF (targetType = D.strStringConst8) OR 
              (targetType = D.strStringConst16) THEN
          (* converting from LONGCHAR string to CHAR string or vice versa *)
          c := D.ConvertString (x. const, targetType);
          IF (c = NIL) THEN
            Sym.ErrT1 (x. pos, 352, D.struct[targetType])
          ELSE
            x. const := c
          END
        ELSIF (src < Opc.subclR) THEN
          IF (dst >= Opc.subclR) THEN
            lreal := x. const. int;
            IF (dst = Opc.subclR) THEN  (* round to REAL *)
              x. const := D.GetRealConst (SHORT (lreal), D.struct[targetType])
            ELSE
              x. const := D.GetRealConst (lreal, D.struct[targetType])
            END
          ELSE
            x. const := GetIntConst (x. const. int)
          END
        ELSIF (src >= Opc.subclR) THEN
          IF (dst < Opc.subclR) THEN
            IF StdTypes.ValidInt (x. const. real) THEN
              x. const := GetIntConst (ENTIER (x. const. real))
            ELSE
              Sym.ErrT1 (x. pos, 352, D.struct[targetType]);
              x. const := GetIntConst (1)
            END
          ELSIF (dst = Opc.subclR) THEN
            (* converting to REAL; make sure that the value is rounded towards 
               REAL precision *)
            IF StdTypes.ValidReal (x. const. real) THEN
              x. const := D.GetRealConst (SHORT (x. const. real), D.struct[targetType])
            ELSE
              Sym.ErrT1 (x. pos, 352, D.struct[targetType]);
              x. const := D.GetRealConst (1, D.struct[targetType])
            END
          ELSE  (* no overflow possible since target is LONGREAL *)
            x. const := D.GetRealConst (x. const. real, D.struct[targetType])
          END
        END;
        (* test int constants for overflow *)
        IF (dst < Opc.subclR) & ~adaptType &
           Int.OutOfRange (x. const. int, dst, err) THEN
          Sym.ErrT1 (x. pos, 352, D.struct[targetType])               
          (* constant not representable as target type *)
        END;
        x. obj := NIL;
        x. currValue := x. const;
        x. type := x. const. type
      ELSE                               (* create conversion instruction *)
        IF (x. currValue IS D.Instruction) & 
           (x. currValue(D.Instruction). opcode DIV Opc.sizeClass = Opc.classConv) THEN
          (* operand is another conversion instruction; determine if the 
             previous operand can be used, possibly turning the other conv into
             dead code, or if we have to use the instruction as operand *)
          oldSrc := SHORT (SHORT (x. currValue(D.Instruction). opndList. arg(D.Const). int));
          oldDst := SHORT (x. currValue(D.Instruction). opcode MOD Opc.sizeClass);
          IF Int.Includes (oldDst, oldSrc) & Int.Includes (dst, src) OR
             Int.Includes (oldSrc, src) & Int.Includes (src, dst) OR
             Int.Includes (src, oldSrc) & Int.Includes (src, dst) & 
               Int.Includes (oldSrc, dst) THEN
            (* we can use the operand, since the old conversion can't cause
               an overflow *)
            arg := x. currValue(D.Instruction). opndList. nextOpnd. arg
          ELSE  
            (* we got something like LONG(SHORT(x)), ie the previous conversion
               (SHORT) may cause an overflow that can't be ignored *)
            arg := x. currValue
          END
        ELSE
          arg := x. currValue
        END;
        (* create new conversion instruction *)
        instr := region. CreateInstruction (Opc.baseConv+dst, D.struct[targetType], pos);
        IF ~Int.Includes (dst, src) &
           ((dst < Opc.subclR) &  StdPragmas.intOverflowCheck. true OR
            (dst >= Opc.subclR) & StdPragmas.realOverflowCheck. true) THEN
          instr. flags := instr. flags + {D.instrNotDead,D.instrCheckOverflow};
          Attr.ContainsRuntimeCheck (region)
        END;
        instr. Operand (D.GetIntConst (src, D.struct[D.strShortInt]));
        instr. Operand (arg);
        Attr.SetOpndPos (instr, x. pos);
        Attr.CreateItem (x, instr, pos)
      END
    END;
    x. pos := pos
  END TypeConversion;

PROCEDURE InsertTempCopy* (region: D.Region; VAR x: Attr.Item): D.Instruction;
(* If `x' refers to the current value of a variable, and if the value of the
   variable can be (directly) replaced by a loop gate during evaluation of the
   following operands (or parameters), then add a copy instruction for the
   current value of `x'.  The procedure `RemoveTempCopy' (called after 
   evaluation of the following operands or parameters) replaces the current
   value in `x' with the argument of the copy instruction.  These two differ
   if a loop gate was introduced in the meantime, changing the argument of the
   copy.
   This compensates for the effect that evaluation of an operand of an dyadic 
   expression or procedure call introduces loop gates for operands written 
   earlier.  If the operands' values are stored only internally (in `x') and 
   written into the GSA code _after_ the following operands have been 
   evaluated, then care must be taken to use the respective loop gate instead 
   of the stored (and superseeded) value.  
   This procedure is called before the second operand of (some) dyadic 
   operations, or the following operand of a procedure have been evaluated,
   respectively.  *)
  VAR
    copy: D.Instruction;
  BEGIN
    IF (region. opcode = Opc.mergeLoop) THEN
      IF (x. obj # NIL) & 
         (x. currValue # NIL) & (x. currValue = x. baseValue) THEN
        copy := region. CreateInstruction (Opc.copy, NIL, D.undefPos);
        copy. Operand (x. currValue);
        RETURN copy
      ELSIF (x. assignment # NIL) &
            (x. assignment IS D.Object) &
            (x. assignment(D.Object). mode = D.objVar) &
            (x. assignment(D.Object). localTo = Sym.currScope) &
            Sym.TypeInGroup (x. assignment(D.Object). type, 
                             D.grpStructured) THEN
        copy := region. CreateInstruction (Opc.copy, NIL, D.undefPos);
        copy. Operand (x. baseValue);
        RETURN copy
      END
    END;
    RETURN NIL
  END InsertTempCopy;

PROCEDURE QueryTempCopy* (VAR x: Attr.Item; VAR tempCopy: D.Instruction;
                           mode: SHORTINT);
(* For an explanation see InsertTempCopy above.  `mode' designates one of the
   following actions: 0=update, 1=update&cleanup, 2=cleanup *)
  BEGIN
    IF (tempCopy # NIL) THEN
      IF (mode # 2) THEN
        IF (x. obj # NIL) & 
           (x. currValue # NIL) & (x. currValue = x. baseValue) THEN
          x. currValue := tempCopy. opndList. arg;
          x. baseValue := x. currValue
        ELSE
          x. baseValue := tempCopy. opndList. arg
        END
      END;
      IF (mode >= 1) THEN
(*        D.Delete (tempCopy);*)
        tempCopy := NIL
      END
    END
  END QueryTempCopy;

PROCEDURE CheckValue* (VAR x: Attr.Item);
(* Emits an error message if `x' is a type, instead of a value.  *)
  BEGIN
    IF (x. obj # NIL) & (x. obj. mode = D.objType) THEN
      E.Err (x. pos, 232)               (* value expected, not data type *)
    END
  END CheckValue;

PROCEDURE Designator* (region: D.Region; VAR x: Attr.Item);
(* Note: The receiver of a type-bound procedure designator is stored in 
   the global variable `receiverDesgiantor'.  *)
  VAR
    obj: D.Object;
    type: D.Struct;
    instr, copy: D.Instruction;
    index, len, size, y, result, memAssign: Attr.Item;
    pos, startPos: LONGINT;
    discardObj: BOOLEAN;
    isVolatileAccess: BOOLEAN;
    
  PROCEDURE Deref (checkForPtr: BOOLEAN);
  (* Executes dereference of a pointer.  If `checkForPtr = TRUE' and the item
     `x' doesn't denote a pointer, an error is generated.  *)
    VAR
      instr: D.Instruction;
      startPos: LONGINT;
    BEGIN
      IF (x. type. form = D.strPointer) THEN
        startPos := S.currSymPos;
        (* create instruction *)
        instr := region. CreateInstruction (Opc.accessHeap, x. type. base, startPos);
        IF StdPragmas.derefCheck. true THEN
          instr. flags := instr. flags+{D.instrCheckNil, D.instrNotDead};
          Attr.ContainsRuntimeCheck (region)
        END;
        instr. Operand (x. type. base);
        Attr.Operand (instr, x);
        AddStructToEnter (region, x. type. base);
        instr. Operand (AccessVar (region, Sym.store));
        (* update item `x' *)
        x. pos := startPos;
        x. adr := x. currValue;
        x. currValue := instr;
        x. type := x. type. base;
        x. assignment := x. type;
        x. baseValue := instr;
        x. arrayDim := 0;
        (* dereference cancels the read-only restriction *)
        x. readOnlyPos := D.undefPos
      ELSIF checkForPtr THEN
        Sym.ErrT1 (S.currSymPos, 228, x. type) (* not pointer *)
      END
    END Deref;
  
  PROCEDURE FieldAddress (VAR x: Attr.Item; field: D.Object): D.Usable;
    VAR
      instr: D.Instruction;
    BEGIN
      instr := region. CreateDyadicOp (Opc.addl, D.struct[D.strAddress], Attr.Adr (region, x), D.GetIntConst (field. offset, D.struct[D.strAddress]), S.currSymPos);
      instr. opndList. pos := S.currSymPos;
      RETURN instr
    END FieldAddress;
  
  PROCEDURE ElementAddress (baseAdr, index, elementSize: D.Usable; pos: LONGINT): D.Usable;
    VAR
      mult, instr, conv: D.Instruction;
    BEGIN
      mult := region. CreateDyadicOp (Opc.multl, D.struct[D.strLongInt], index, elementSize, pos);
      mult. opndList. pos := pos;
      IF (D.strAddress # D.strLongInt) THEN
        (* convert LONGINT offset into a value of address value *)
        conv := region. CreateInstruction (Opc.baseConv+Opc.subclAdr, D.struct[D.strAddress], pos);
        conv. Operand (D.GetIntConst (Opc.subclL, D.struct[D.strShortInt]));
        conv. Operand (mult);
        mult := conv
      END;
      instr := region. CreateDyadicOp (Opc.addl, D.struct[D.strAddress], baseAdr, mult, pos);
      instr. opndList. pos := pos;
      RETURN instr
    END ElementAddress;
  
  PROCEDURE FixPosition (access: D.Instruction);
  (* Fix position of pointer base.  *)
    VAR
      rvalue, adr: D.Instruction;
    BEGIN
      IF (access. opndList. arg IS D.Instruction) THEN
       rvalue := access. opndList. arg(D.Instruction);
       IF (rvalue. opcode = Opc.accessHeap) THEN
         adr := access. opndList. nextOpnd. arg(D.Instruction);
         adr. opndList. pos := rvalue. opndList. nextOpnd. pos
       END
     END
    END FixPosition;
  
  PROCEDURE AbstractSuperCall (tbProc: D.Object; base: D.Struct): BOOLEAN;
    VAR
      obj: D.Object;
    BEGIN  (* pre: tb proc `tbProc.name' exists in `base' *)
      obj := Sym.FindField (base, tbProc. name^);
      RETURN (D.objAbstractTBProc IN obj. flags)
    END AbstractSuperCall;
  
  BEGIN  (* pre: (S.sym = ident) *)
    isVolatileAccess := FALSE;
    Qualident (x);
    (* update additional item fields *)
    x. type := x. obj. type;
    CASE x. obj. mode OF
    | D.objConst:
      x. const := x. obj. data(D.Const);
      x. currValue := x. const;
      x. baseValue := x. currValue
    | D.objVar, D.objVarPar:
      x. assignment := x. obj;
      x. currValue := AccessVar (region, x. obj);
      x. baseValue := x. currValue;
      x. basePos := x. pos;
      (* variable record parameter is accompanied by its type tag, an open 
         array by its length information; store the object in `ttHint' in order
         to retrieve the type tag and length parameter later on *)
      IF (x. obj. mode = D.objVarPar) & (x. type. form = D.strRecord) &
           ~(D.objNoTypeTag IN x. obj. flags) OR
         (x. type. form = D.strOpenArray) THEN
        x. ttHint := x. obj
      END;
      (* check whether the variable is read only *)
      IF Sym.ImportedObject (Sym.mod, x. obj) &
           (D.objIsExportedReadOnly IN x. obj. flags) THEN
        x. readOnlyPos := x. pos
      ELSIF DegenerateValueParam (x. obj) THEN
        (* open array value parameter, but no information about the array's
           length; this means we cannot create a local copy of the parameter,
           therefore the parameter should not be modified locally; this is
           not sufficient to guarantee correctness (the parameter's value can
           be modified if it is visible by other names), but it is a close
           approximation *)
        x. readOnlyPos := -x. pos
      END;
      IF (D.objVolatile IN x. obj. flags) THEN
        isVolatileAccess := TRUE
      END
    | D.objProc:
      IF (x. obj. localTo # Sym.predef) & (x. obj. localTo # Sym.system) THEN
        (* not a predefined procedure *)
        x. adr := region. CreateAdrInstr (x. obj, S.currSymPos);
        x. currValue := x. adr
      END
    | D.objType:
      x. currValue := D.constUndef
    ELSE
    END;
    
    IF (x. obj. mode # D.objType) THEN
      LOOP
        (* if the current value is a pointer, store its address as the 
           place to look for the type tag or length information; don't
           touch ttHint if the pointer hasn't a dynamic type (e.g. if
           it's a C pointer) *)
        IF (x. type. form = D.strPointer) &
           ~(D.structStaticPointer IN x. type. flags) THEN
          x. ttHint := x. currValue
        END;
        
        discardObj := TRUE;
        IF (S.sym = S.period) THEN
          (* record selector, may be a field or a type-bound procedure *)
          type := x. type;
          IF (type. form = D.strPointer) THEN
            type := type. base
          END;
          
          (* enable underscore if it is allowed for record fields *)
          S.allowUnderscore := (D.structAllowsUnderscore IN type. flags);
          S.GetSym;
          S.allowUnderscore := (D.objAllowsUnderscore IN Sym.mod. flags);
          
          IF (type. form # D.strRecord) THEN
            Sym.ErrT1 (x. pos, 227, type); (* not a record *)
            x. type := D.struct[D.strUndef]
          ELSIF (S.sym # S.ident) THEN
            E.Err (S.currSymPos, 100);  (* identifier expected *)
            x. type := D.struct[D.strUndef]
          ELSE
            obj := Sym.FindField (type, S.str^);
            IF (obj = NIL) THEN
              E.Err (S.currSymPos, 197); (* undeclared identifier *)
              x. type := D.struct[D.strUndef];
              S.GetSym
              
            ELSIF (obj. mode = D.objField) THEN (* record field *)
              Deref (FALSE);
              x. adr := FieldAddress (x, obj);
              x. type := obj. type;
              instr := region. CreateInstruction (Opc.accessField, obj. type, S.currSymPos);
              Attr.Operand (instr, x);   (* record value *)
              instr. Operand (Attr.Adr (region, x)); (* field address *)
              instr. Operand (obj);    (* field object *)
              FixPosition (instr);
              x. currValue := instr;
              x. pos := S.currSymPos;
              x. ttHint := NIL;
              (* check if accessing an read-only field *)
              IF Sym.ImportedObject (Sym.mod, obj) &
                 (D.objIsExportedReadOnly IN obj. flags) &
                 (x. readOnlyPos = D.undefPos) THEN
                x. readOnlyPos := S.currSymPos
              END;
              IF (D.objVolatile IN obj. flags) THEN
                isVolatileAccess := TRUE
              END;
              S.GetSym
              
            ELSE  (* (obj. mode = objTBProc); type-bound procedure *)
              (* make sure that the receiver matches the designator type and
                 do a deref if the receiver is a record type *)
              IF (obj. data(D.Object). mode = D.objVarPar) THEN
                Deref (FALSE)
              ELSIF (obj. data(D.Object). type. form = D.strPointer) &
                    (x. type. form = D.strRecord) THEN
                Sym.ErrT1 (x. pos, 239, obj. data(D.Object). type)
                (* not assignment compatible to receiver type *)
              END;
              receiverDesignator := x;
              (* store procedure object in `x. obj', type tag in `x. ttHint', 
                 receiver value in `x. currValue', address of receiver in `x. 
                 baseValue', and (dynamic) address of called procedure in 
                 `x. adr' *)
              x. pos := S.currSymPos;
              S.GetSym;
              
              IF (D.structVTableField IN type. flags) THEN
                (* no type tag, but record has virtual method table *)
                x. ttHint := x. currValue
              ELSE
                (* get type tag and store it in x.ttHint  *)              
                IF (S.sym = S.arrow) THEN (* super call: use static base type *)
                  x. ttHint := Attr.TypeTag (region, x, 1)
                ELSE                      (* use dynamic type *)
                  x. ttHint := Attr.TypeTag (region, x, -1)
                END
              END;
              
              x. adr := D.constUndef;  (* use this value in case of error *)
              IF (S.sym = S.arrow) THEN  (* this is a super call *)
                IF (type. base = NIL) THEN
                  Sym.ErrT1 (x. pos, 229, type) (* type has no base type *)
                ELSIF (Sym.BaseDefinition (obj. data(D.Object), 
                                           obj. name^) = NIL) THEN
                  E.ErrIns (x. pos, 230, obj. name^)
                  (* type-bound procedure not defined in base type *)
                ELSIF AbstractSuperCall (obj, type. base) THEN
                  E.Err (x. pos, 454)
                  (* passing control to inherited abstract procedure *)
                ELSIF (D.structNoDescriptor IN type. base. flags) THEN
                  E.Err (x. pos, 457)    (* can't do super call *)
                ELSE
                  obj := Sym.BaseDefinition (obj. data(D.Object), obj. name^);
                  x. adr := Attr.TBProcAdr (region, x. ttHint, type. base, 
                                            obj, S.currSymPos, TRUE)
                END;
                S.GetSym
              ELSE
                x. adr := Attr.TBProcAdr (region, x. ttHint, type, obj, x. pos,
                                          D.objFinalTBProc IN obj. flags)
              END;
              
              x. obj := obj;             (* tb proc object *)
              x. type := obj. type;      (* formal parameters of tb proc *)
              IF (obj. data(D.Object). mode = D.objVar) THEN
                (* record receiver's address in x.baseValue *)
                x. baseValue := Attr.Adr (region, x)
              END
            END
          END;
          x. arrayDim := 0
          
        ELSIF (S.sym = S.lBrak) THEN
          Deref (FALSE);
          REPEAT
            (* test whether current item is an array *)
            IF ~Sym.TypeInGroup (x. type, D.grpArray) THEN
              Sym.ErrT1 (x. pos, 243, x. type);
              (* not an array (is `x. type') *)
              x. type := D.struct[D.strUndef]
            END;
            startPos := S.currSymPos;
            S.GetSym;                    (* skip `[' or ',' *)
            
            copy := InsertTempCopy (region, x);
            Expr (region, index);
            CheckValue (index);
            QueryTempCopy (x, copy, 1);
            RedoDesignatorAccess (region, x);
            CheckType (index. type, D.grpInteger, index. pos);
            IF (x. type. form # D.strUndef) THEN
              TypeConversion (region, index, D.strLongInt, FALSE, index. pos);
              
              IF Attr.HasLengthInfo (x, 0) THEN
                (* create boundary check if `x' is a proper Oberon array; if 
                   it's e.g. a C array, then use the index unchecked *)
                Attr.ArrayLength (region, x, 0, index. pos, FALSE, len);
                instr := Attr.DyadicOp (region, Opc.boundIndex, index. type, 
                                        index, len, index. pos);
                INCL (instr. flags, D.instrNotDead);
                IF StdPragmas.indexCheck. true THEN
                  Attr.ContainsRuntimeCheck (region)
                ELSE
                  INCL (instr. flags, D.instrIsDisabled)
                END;
                EvalInstr (index, instr)
              END;
              
              (* calculate element address *)
              Attr.SizeOfItem (region, x, 1, startPos, size);
              x. adr := ElementAddress (Attr.Adr (region, x), index. currValue,
                                                     size. currValue, startPos)
            ELSE
              x. adr := D.GetIntConst (0, D.struct[D.strAddress])
            END;
            x. type := x. type. base;
            
            instr := region. CreateInstruction (Opc.accessElement, x. type, S.currSymPos);
            Attr.Operand (instr, x);     (* array value *)
            instr. Operand (Attr.Adr (region, x));   (* element address *)
            Attr.Operand (instr, index); (* array index *)
            FixPosition (instr);
            INC (x. arrayDim);
            x. currValue := instr;
            x. pos := S.currSymPos;
            IF (x. type. form # D.strOpenArray) THEN
              x. ttHint := NIL
            END
          UNTIL (S.sym # S.comma);
          S.CheckSym (S.rBrak)
          
        ELSIF (S.sym = S.arrow) THEN
          Deref (TRUE);
          S.GetSym
          
        ELSIF (S.sym = S.lParen) & 
              ((x. type. form = D.strRecord) OR
               (x. type. form = D.strPointer) & 
                 (x. type. base. form = D.strRecord)) THEN
          (* only interpret an opening parenthesis as type guard if the 
             designator has an appropriate type; otherwise assume it belongs
             to a procedure call and leave the designator rule *)
          S.GetSym;
          TypeQualident (type, pos);
          S.CheckSym (S.rParen);
          Attr.CreateItem (y, type, pos);
          TypeTest (region, x, y, TRUE, y. pos, result);
          IF (result. currValue IS D.Instruction) &
             (result. currValue(D.Instruction). opcode = Opc.accessHeap) THEN
            (* the record guard changed the type of the heap access, adjust
               designator data accordingly *)
            x. assignment := 
                     result. currValue(D.Instruction). opndList. arg(D.Struct);
            x. baseValue := result. currValue
          END;
          x. currValue := result. currValue;
          x. type := type;
          x. adr := Attr.Adr (region, x); (* calculate address of tested var *)
          discardObj := FALSE
          
        ELSE
          EXIT
        END;
        IF discardObj & (x. obj # NIL) & (x. obj. mode # D.objTBProc) THEN
          x. obj := NIL
        END;
        IF (x. type. form = D.strUndef) THEN
          x. adr := D.GetIntConst (0, D.struct[D.strAddress]);
          x. readOnlyPos := D.undefPos  (* invalidate read-only info *)
        END;
        x. const := NIL
      END
    END;
    IF (x. basePos >= 0) THEN
      x. pos := x. basePos
    END;
    
    IF isVolatileAccess THEN
      instr := region. CreateInstruction (Opc.accessMem, x. type, x. pos);
      INCL (instr. flags, D.instrUniqueResult);
      instr. Operand (Attr.Adr (region, x));
      instr. Operand (AccessVar (region, Sym.mem));
      instr. SetOpndSymLoc (Sym.mem);
      instr. Operand (AccessVar (region, Sym.store));
      instr. SetOpndSymLoc (Sym.store);
      Attr.CreateItem (memAssign, instr. AppendResult (D.CreateSymLocation (Sym.mem, D.symLocObject), NIL), x. pos);
      AssignToVar (region, Sym.mem, memAssign);
      ReclaimFromMem (instr);
      x. obj := NIL;             (* don't treat this as an ordinary variable *)
      x. currValue := instr
    END
  END Designator;

PROCEDURE StringConvertible* (VAR expr: Attr.Item; target: D.Struct): BOOLEAN;
(* TRUE iff `expr' is a string constant or it was possible to convert `expr' 
   into one, ie, if `expr' is a character constant.  In the later case the 
   type of the expression is changed to string const as a side effect.
   If `target' is a LONGCHAR values, a LONGCHAR string constant, or an array of
   LONGCHAR, then the produced value is a LONGCHAR string constant.  *)
  VAR
    s: ARRAY 5 OF CHAR;
    targetForm: SHORTINT;
    len: LONGINT;
  BEGIN
    IF (target. form = D.strChar16) OR
       (target. form = D.strStringConst16) OR
       Sym.TypeInGroup (target, D.grpArray) & (target. base. form = D.strChar16) THEN
      targetForm := D.strStringConst16
    ELSE
      targetForm := D.strStringConst8
    END;
    
    IF (expr. type. form = targetForm) THEN
      RETURN TRUE
    ELSIF (expr. const # NIL) & Sym.TypeInGroup (expr. type, D.grpChar) &
          (expr. type. form+(D.strStringConst8-D.strChar8) <= targetForm) THEN
      (* converting character constant to string constant *)
      expr. type := D.struct[targetForm];
      s := "XX"; s[3] := 0X;
      IF (targetForm = D.strStringConst8) THEN
        IF (StdTypes.minChar8 <= expr. const. int) &
           (expr. const. int <= StdTypes.maxChar8) THEN
          s[0] := CHR (expr. const. int)
        END;
      ELSE  (* targetForm = D.strConst16 *)
        IF (StdTypes.minChar16 <= expr. const. int) &
           (expr. const. int <= StdTypes.maxChar16) THEN
          s[0] := CHR (expr. const. int DIV 256);
          s[1] := CHR (expr. const. int MOD 256)
        END
      END;
      IF (expr. const. int = 0) THEN
        len := 0
      ELSE
        len := 1
      END;
      expr. const := D.GetStringConst (s, len, D.struct[targetForm]);
      expr. obj := NIL;
      expr. currValue := expr. const;
      RETURN TRUE
    ELSIF (expr. type. form = D.strStringConst8) &
          (targetForm = D.strStringConst16) THEN
      (* converting CHAR string constant to LONGCHAR string constant *)
      TypeConversion (NIL, expr, targetForm, FALSE, expr. pos);
      RETURN TRUE
    ELSE
      RETURN FALSE
    END
  END StringConvertible;


PROCEDURE CheckOperandType (VAR x: Attr.Item; 
                            legalTypes, legalTypeGroups: SET): SHORTINT;
  VAR
    i: SHORTINT;
  BEGIN
    IF (x. obj # NIL) & (x. obj. mode = D.objType) THEN
      E.Err (x. pos, 232);             (* value expected, not data type *)
      RETURN -1
    ELSE
      IF (x. type. form IN legalTypes) THEN
        i := x. type. form
      ELSE
        i := MAX (SET)+1;
        WHILE (i <= 2*MAX (SET)+1) &
              ~(((i+D.grpOffset) IN legalTypeGroups) & 
                Sym.TypeInGroup (x. type, i)) DO
          INC (i)
        END
      END;
      IF (i > 2*MAX (SET)+1) THEN
        Sym.ErrT1 (x. pos, 231, x. type);
        (* operator not applicable to type *)
        RETURN -1
      ELSE
        RETURN i
      END
    END
  END CheckOperandType;

PROCEDURE EvalMonadicOp* (region: D.Region; VAR x: Attr.Item; opcClass: INTEGER; 
                          pos: LONGINT; opndTypes, opndTypeGroups: SET);
  VAR
    right: SHORTINT;
    instr: D.Instruction;
  BEGIN
    (* check operand types for compability *)
    right := CheckOperandType (x, opndTypes, opndTypeGroups);
    IF (opcClass = Opc.classSub) THEN
      IF (right = D.grpSet) THEN
        opcClass := Opc.classCompl
      ELSE
        opcClass := Opc.classNeg
      END
    END;
    
    IF (opcClass # Opc.classAdd) THEN    (* ignore monadic `+' *)
      (* calculate result of operation *)
      instr := region. CreateInstruction (opcClass*Opc.sizeClass+
                      D.OperatorSubclass (x. type, 0), x. type, pos);
      Attr.Operand (instr, x);
      IF (right >= 0) THEN
        EvalInstr (x, instr)
      ELSE
        Attr.CreateItem (x, instr, instr. pos)
      END
    END
  END EvalMonadicOp;

PROCEDURE EvalDyadicOp* (region: D.Region; VAR x, y: Attr.Item; 
                         opcClass: INTEGER; pos: LONGINT; 
                         opndTypes, opndTypeGroups: SET);
  VAR
    form, left, right, subclass: SHORTINT;
    mismatch: BOOLEAN;
    instr: D.Instruction;
    resultType: D.Struct;
    opc: INTEGER;
  BEGIN
    (* check operand types for compability *)
    left := CheckOperandType (x, opndTypes, opndTypeGroups);
    right := CheckOperandType (y, opndTypes, opndTypeGroups);
    IF (left >= 0) & (right >= 0) THEN
      (* check rhs for compability with lhs *)
      mismatch := (left # right);
      CASE left OF
      | D.strNil:
        mismatch := ~Sym.TypeInGroup (y. type, D.grpNilCompat)
      | D.grpProc:
        (* the left hand side of the expression is a procedure variable or a
           procedure; a comparison is only legal if
           a) the right side has the same type as the left side
           b) the right side is NIL
           c) the left or the right side is a procedure, and the formal 
              parameter lists of both operands match
           Note that case c) isn't legal if you follow the report by the 
           letter; but this is most likely an oversight by the language
           designers, since it introduces asymmetric behaviour with regard 
           to the rules for assignment compatibility; this behviour is enforced
           if the pragma variable `ConformatMode' is TRUE *)
        IF (right = D.strNil) OR (x. type = y. type) THEN
          mismatch := FALSE
        ELSIF (right # D.grpProc) OR 
              ~Sym.ParamsMatch (x. type, y. type, FALSE) OR
              StdPragmas.conformantMode. true THEN
          mismatch := TRUE
        ELSE (* allow to compare procedure values if formal parameters match *)
          mismatch := FALSE
        END
      | D.grpPointer:
        mismatch := (right # D.strNil) &
                    ((right # D.grpPointer) OR 
                     ~(Sym.SameType (x. type, y. type) OR
                       Sym.ExtensionOf (x. type, y. type) OR
                       Sym.ExtensionOf (y. type, x. type)))
      | D.strPtr:
        mismatch := (right # D.strPtr) & (right # D.strNil)
      | D.grpSet:  (* need same type on both sides of set operation *)
        mismatch := (x. type # y. type)
      ELSE
        IF (Opc.classEql <= opcClass) & (opcClass <= Opc.classGeq) &
           mismatch THEN
          (* deal with the special case of comparing a string to a character 
             constant by converting the char const into a string const of 
             length 1 *)
          IF (left = D.grpString8) OR (left = D.grpString16) THEN
            mismatch := ~StringConvertible (y, x. type);
          END;
          IF mismatch & ((right = D.grpString8) OR (right = D.grpString16)) THEN
            mismatch := ~StringConvertible (x, y. type)
          END
        END;
      END;
      IF mismatch THEN
        Sym.ErrT1 (y. pos, 233, x. type)
      END;
      
      (* adjust operator to set arithmetic if necessary *)
      IF (left = D.grpSet) THEN
        CASE opcClass OF
        | Opc.classAdd    : opcClass := Opc.classUnion
        | Opc.classSub    : opcClass := Opc.classDiff
        | Opc.classMult   : opcClass := Opc.classInter
        | Opc.classDivReal: opcClass := Opc.classSymDiff
        ELSE (* Opc.classNeq, Opc.classEql *)
        END
      END
    ELSE
      mismatch := TRUE
    END;
    
    (* determine result type *)
    form := x. type. form;
    IF (form < y. type. form) & (y. type. form < D.strSet8) THEN
      (* avoid using a non-numeric type as result; otherwise we build for 
         faulty code like `1+{}' an integer operation with a result type of
         SET, which would confuse constant folding *)
      form := y. type. form
    END;
    IF (opcClass = Opc.classDivReal) & (form < D.strReal) THEN
      form := D.strReal
    ELSIF (form >= D.strNone) & (form # D.strPointer) & (form # D.strProc) THEN
      (* prevent `form' from taking on any invalid structure ids, e.g. if the
         user used a record as argument; relations involving pointer or 
         procedure value are valid *)
      form := D.strBoolean
    END;
    IF (Opc.classEql <= opcClass) & (opcClass <= Opc.classGeq) THEN
      resultType := D.struct[D.strBoolean]
    ELSE
      resultType := D.struct[form]
    END;
    
    (* adjust operand types *)
    IF (D.strChar8 <= form) & (form < D.strComplex) THEN
      TypeConversion (region, x, form, FALSE, x. pos);
      TypeConversion (region, y, form, FALSE, y. pos)
    END;
    
    (* calculate result of operation *)
    IF (left = D.grpString16) OR (right = D.grpString16) THEN
      subclass := Opc.subclLStr
    ELSIF (left = D.grpString8) OR (right = D.grpString8) THEN
      subclass := Opc.subclStr
    ELSE
      subclass := D.OperatorSubclass (NIL, form)
    END;
    opc := opcClass*Opc.sizeClass+subclass;
    instr := region. CreateInstruction (opc, resultType, pos);
    Attr.Operand (instr, x);
    Attr.Operand (instr, y);
    IF (Opc.classEql <= opcClass) & (opcClass <= Opc.classGeq) &
       ((subclass = Opc.subclStr) OR (subclass = Opc.subclLStr)) THEN
      (* comparing two strings: add addresses of first and second operand to
         instruction *)
      instr. Operand (Attr.Adr (region, x));
      instr. Operand (Attr.Adr (region, y))
    END;
    IF mismatch THEN
      Attr.CreateItem (x, instr, instr. pos)
    ELSE
      EvalInstr (x, instr)
    END
  END EvalDyadicOp;

PROCEDURE IsCondResult* (gate: D.Gate): BOOLEAN;
  BEGIN
    RETURN (gate. opndList. nextOpnd. arg = Sym.constTrue) &
           (gate. opndList. nextOpnd. nextOpnd. arg = Sym.constFalse)
  END IsCondResult;

PROCEDURE SplitPaths* (region: D.Region; VAR cond: Attr.Item; 
                       VAR truePath, falsePath: D.Region);
(* Splits control into two paths `truePath' and `falsePath' depending on 
   `cond'.  The `cond' is a gate resulting from an OR or an & operation in the
   same region that isn't bound to a variable, then the boolean operator is
   modified to contain a true and a false path which are returned.  Otherwise
   two paths are created and placed in `region'.  *)
  VAR
    merge: D.Merge;
    x: Attr.Item;
    h: D.Region;
    not: D.Instruction;
  BEGIN
    IF (cond. currValue IS D.Gate) &
       IsCondResult (cond. currValue(D.Gate)) THEN
      (* `cond' is not the content of a variable and corresponds to a 
         gate with the operands TRUE and FALSE *)
      merge := cond. currValue(D.Gate). opndList. arg(D.Merge);
      truePath := merge. opndList. arg(D.Region);
      falsePath := merge. opndList. nextOpnd. arg(D.Region)
    ELSIF (cond. currValue IS D.Instruction) &
          (cond. currValue(D.Instruction). opcode = Opc.notsu) THEN
      not := cond. currValue(D.Instruction);
      Attr.InitItem (x, cond. pos);
      x. currValue := cond. currValue(D.Instruction). opndList. arg;
      SplitPaths (region, x, truePath, falsePath);
      h := truePath; truePath := falsePath; falsePath := h;
      not. Delete()
      (* only reference once by function calling SplitPaths; can be discarded 
         because the calling function will use only the swapped paths *)
    ELSE
      (* the condition is either a variable, a constant, an instruction, or
         a gate that isn't part of a condition merge or that is placed in 
         another region *)
      truePath := D.CreateGuard (cond. currValue, Opc.guardTrue, cond. pos);
      Attr.SetOpndPos (truePath, cond. pos);
      falsePath := D.CreateGuard (cond. currValue, Opc.guardFalse, cond. pos);
      Attr.SetOpndPos (falsePath, cond. pos);
      region. Insert (truePath);
      region. Insert (falsePath)
    END
  END SplitPaths;

PROCEDURE SplitIfPaths* (region: D.Region; VAR cond: Attr.Item; 
                         VAR truePath,falsePath: D.Region; VAR merge: D.Merge);
(* Splits `cond' into two paths `truePath' and `falsePath', and merges them 
   a "merge-if:" node.  *)
  BEGIN
    SplitPaths (region, cond, truePath, falsePath);
    IF (truePath. merge # NIL) & (truePath. merge = falsePath. merge) THEN
      merge := truePath. merge;
      merge. opcode := Opc.mergeIf
    ELSE
      merge := D.CreateMerge (Opc.mergeIf);
      merge. Operand (truePath);
      merge. Operand (falsePath);
      region. Insert (merge);
      truePath. merge := merge;
      falsePath. merge := merge
    END
  END SplitIfPaths;

PROCEDURE BoundSetElement* (region: D.Region; form: SHORTINT; 
                            VAR element: Attr.Item);
(* Creates bound operator on `element', returns result in `element'.  *)
  VAR
    instr: D.Instruction;
    bound: D.Const;
  BEGIN
    CheckType (element. type, D.grpInteger, element. pos);
    IF (form = D.strUndef) THEN
      form := D.strSet32
    END;
    bound := StdTypes.Max (form);
    bound := D.GetIntConst (bound. int+1, D.struct[D.strShortInt]);
    instr := region. CreateDyadicOp (Opc.boundRange, element. type, element. currValue, bound, element. pos);
    instr. opndList. pos := element. pos;
    INCL (instr. flags, D.instrNotDead);
    IF StdPragmas.rangeCheck. true THEN
      Attr.ContainsRuntimeCheck (region)
    ELSE
      INCL (instr. flags, D.instrIsDisabled)
    END;
    EvalInstr (element, instr)
  END BoundSetElement;

PROCEDURE Factor (region: D.Region; VAR x: Attr.Item);
  VAR
    pos: LONGINT;
    exitInfo: Attr.ExitInfo;
    designator: BOOLEAN;
    
  PROCEDURE Set (type: D.Struct);
    VAR
      y: Attr.Item;
      
    PROCEDURE Element (VAR x: Attr.Item);
      VAR
        instr: D.Instruction;
        left, right: Attr.Item;
      BEGIN
        Expr (region, left);
        CheckValue (left);
        BoundSetElement (region, type. form, left);
        IF (S.sym = S.upto) THEN
          S.GetSym;
          Expr (region, right);
          CheckValue (right);
          BoundSetElement (region, type. form, right)
        ELSE
          right := left
        END;
        IF (left. const # NIL) & (right. const # NIL) &
           (left. const. int > right. const. int) THEN
          E.Err (left. pos, 236)  
          (* lower bound has to be less or equal to upper bound *)
        END;
        (* create set range *)
        instr := Attr.DyadicOp (region, 
                            Opc.baseBitRange+D.OperatorSubclass (type, 0),
                            type, left, right, left.pos);
        EvalInstr (x, instr)
      END Element;

    BEGIN  (* pre: S.sym = S.lBrace *)
      S.GetSym;
      IF (S.sym # S.rBrace) THEN
        Element (x);
        WHILE (S.sym = S.comma) DO
          pos := S.currSymPos;
          S.GetSym;
          Element (y);
          EvalDyadicOp (region, x, y, Opc.classAdd, pos, 
            {}, 
            {D.grpSet+D.grpOffset})
        END
      ELSE                               (* empty set *)
        Attr.CreateItem (x, D.GetSetConst ({}, type), S.currSymPos)
      END;
      S.CheckSym (S.rBrace)
    END Set;
  
  BEGIN
    Attr.InitItem (x, S.currSymPos);
    designator := FALSE;
    IF (S.sym = S.ident) THEN            (* variable or function call *)
      Designator (region, x);
      IF (S.sym = S.lParen) OR (x. obj # NIL) & (x. obj. mode = D.objTBProc) THEN
        ProcedureCall (region, x, x, exitInfo, FALSE);
        (* if the result type is a pointer, set reference to the dynamic type;
           see also procedure Designator *)
        IF (x. type. form = D.strPointer) &
           ~(D.structStaticPointer IN x. type. flags) THEN
          x. ttHint := x. currValue
        END
      ELSIF (x. obj # NIL) & (x. obj. mode = D.objType) &
            Sym.TypeInGroup (x. type, D.grpSet) & (S.sym = S.lBrace) THEN
        (* name of set type followed by by left brace: set constructor *)
        Set (x. type)
      ELSE
        designator := TRUE
      END
    ELSIF (S.sym = S.number) THEN        (* numeric constant *)
      CASE S.numType OF
      | S.numInt:                        (* integer *)
        x. const := D.GetIntConst (S.intVal, StdTypes.IntType (S.intVal))
      | S.numReal:                       (* REAL *)
        x. const := D.GetRealConst (S.realVal, D.struct[D.strReal])
      | S.numLReal:                      (* LONGREAL *)
        x. const := D.GetRealConst (S.realVal, D.struct[D.strLongReal])
      END;
      S.GetSym
    ELSIF (S.sym = S.string) THEN        (* string or char constant *)
      IF (Strings.Length (S.str^) <= 1) THEN (* char const *)
        x. const := D.GetIntConst (S.intVal, StdTypes.CharType (S.intVal))
      ELSE
        x. const := D.GetStringConst (S.str^, Strings.Length (S.str^),
                                      D.struct[D.strStringConst8])
      END;
      S.GetSym
    ELSIF (S.sym = S.nil) THEN           (* NIL constant *)
      x. const := D.constNil;
      S.GetSym
    ELSIF (S.sym = S.lBrace) THEN        (* set value *)
      Set (D.struct[D.strSet32])
    ELSIF (S.sym = S.lParen) THEN        (* parenthesis *)
      S.GetSym;
      Expr (region, x);
      S.CheckSym (S.rParen)
    ELSIF (S.sym = S.not) THEN           (* boolean not *)
      pos := S.currSymPos;
      S.GetSym;
      Factor (region, x);
      EvalMonadicOp (region, x, Opc.classNot, pos, {D.strBoolean}, {})
    ELSE
      E.Err (S.currSymPos, 181);  (* factor starts with illegal symbol *)
      x. type := D.struct[D.strUndef];
      x. currValue := Sym.constFalse;    (* any value should do *)
      S.GetSym  (* skip symbol to prevent infinite loop *)
    END;
    x. designator := designator;
    IF (x. type = NIL) THEN              (* complete constant item *)
      x. type := x. const. type;
      x. currValue := x. const
    END
  END Factor;

PROCEDURE SwitchMergeOpnds (u: D.Usable; count: INTEGER): BOOLEAN;
  VAR
    gate: D.Gate;
  BEGIN
    IF (u IS D.Instruction) & (u(D.Instruction). opcode = Opc.notsu) THEN
      RETURN SwitchMergeOpnds (u(D.Instruction). opndList. arg, count+1)
    ELSIF (u IS D.Gate) THEN
      gate := u(D.Gate);
      IF (gate. opndList. nextOpnd. arg = Sym.constTrue) &
         (gate. opndList. nextOpnd. nextOpnd. arg = Sym.constFalse) THEN
        RETURN ODD (count)
      ELSE
        RETURN FALSE
      END
    ELSE
      RETURN FALSE
    END
  END SwitchMergeOpnds;

PROCEDURE FixOldValues (path: D.Region);
(* Looks through the gates belonging to the given path.  If the gates' 
   `oldValue' refers to an outdated value (i.e., it does not correspond to the
   other gate argument), replace `oldValue' with the argument corresponding
   to `path'.  [Ok, this seems to help, even if I don't know why it should
   not break anything.]  *)
  VAR
    merge: D.Merge;
    opn, opn0: INTEGER;
    use: D.Opnd;
    gate: D.Gate;
  BEGIN
    merge := path. RegionMerge();
    opn := merge. ArgumentIndex (path)+1;
    IF (opn = 2) THEN
      opn0 := 1
    ELSE
      opn0 := 2
    END;
    use := merge. useList;
    WHILE (use # NIL) DO
      IF (use. instr IS D.Gate) & (use. instr(D.Gate). var # NIL) THEN
        gate := use. instr(D.Gate);
        IF (gate. NthArgument (opn0) # gate. oldValue) THEN
          gate. oldValue := gate. NthArgument (opn)
        END
      END;
      use := use. nextUse
    END
  END FixOldValues;

PROCEDURE InsertGatePlaceholders (r: D.Region);
(* For every region in `r' that has no corresponding merge (i.e., for which
   `RegionMerge' returns NIL), and that is a direct child of `r', insert 
   placeholders that keep track of the values of `r's gate operands.  These
   values are later used to reconstruct gates that combine paths from the
   children of `r'.  *)
  VAR
    rMerge: D.Merge;
    opn: INTEGER;
    r0: D.Region;
    instr, hint: D.Instruction;
    
  PROCEDURE NoGateExists (r: D.Region; var: D.Object): BOOLEAN;
    VAR
      instr: D.Instruction;
    BEGIN
      instr := r. instrList;
      WHILE (instr # NIL) DO
        IF (instr IS D.Gate) & (instr(D.Gate). var = var) THEN
          RETURN FALSE
        END;
        instr := instr. nextInstr
      END;
      RETURN TRUE
    END NoGateExists;
  
  BEGIN
    rMerge := r. RegionMerge();
    IF (rMerge # NIL) THEN
      opn := rMerge. ArgumentIndex (r)+1;
      r0 := r. regionList;
      WHILE (r0 # NIL) DO
        IF (r0. RegionMerge() = NIL) THEN
          instr := rMerge. instrList;
          WHILE (instr # NIL) DO
            IF (instr IS D.Gate) & (instr(D.Gate). var # NIL) &
               NoGateExists (r0, instr(D.Gate). var) THEN
              hint := r0. CreateInstruction (Opc.noopGateHint, 
                                             NIL, D.undefPos);
              hint. Operand (instr(D.Gate). var);
              hint. Operand (instr(D.Gate). NthArgument (opn))
            END;
            instr := instr. nextInstr
          END;
        END;
        r0 := r0. nextRegion
      END
    END
  END InsertGatePlaceholders;

PROCEDURE CondAnd (region: D.Region; VAR x: Attr.Item; rhs: D.Usable; negate: BOOLEAN);
  VAR
    y: Attr.Item;
    dummy: SHORTINT;  
    gate: D.Gate;  
    switched: BOOLEAN;
    merge, merge2, oldMerge, oldMerge2: D.Merge; 
    truePath, falsePath, truePath2, falsePath2: D.Region;
  BEGIN
    dummy := CheckOperandType (x, {D.strBoolean}, {});
    switched := SwitchMergeOpnds (x. currValue, 0);
    SplitIfPaths (region, x, truePath, falsePath, merge);
    merge. opcode := Opc.mergeCond;
    ResetVariables (merge, truePath);
    IF (rhs = NIL) THEN
      IF (x. obj # NIL) & (x. obj. name[0] = "$") THEN
        (* left side is either $exit or $return *)
        Expr (truePath, y)
      ELSE
        Factor (truePath, y)
      END;
      dummy := CheckOperandType (y, {D.strBoolean}, {})
    ELSE 
      Attr.InitItem (y, x. pos);
      y. type := D.struct[D.strBoolean];
      y. currValue := rhs
    END;
    IF negate THEN
      EvalMonadicOp (truePath, y, Opc.classNot, y. pos, {D.strBoolean}, {})
    END;
    
    SplitPaths (truePath, y, truePath2, falsePath2);
    oldMerge2 := falsePath2. merge;
    IF switched THEN
      InsertGatePlaceholders (merge. opndList. nextOpnd. arg(D.Region));
      merge. opndList. nextOpnd. ReplaceOperand (falsePath2)
    ELSE
      InsertGatePlaceholders (merge. opndList. arg(D.Region));
      merge. opndList. ReplaceOperand (falsePath2)
    END;
    falsePath2. merge := merge;
    
    merge2 := D.CreateMerge (Opc.mergeCond);
    oldMerge := truePath2. RegionMerge();
    merge2. Operand (truePath2);
    merge2. Operand (merge);
    region. Insert (merge2);
    truePath2. merge := merge2;
    merge. merge := merge2;
    
    gate := merge2. CreateGate (Opc.gate, NIL, D.struct[D.strBoolean]);
    gate. Operand (Sym.constTrue);
    gate. Operand (Sym.constFalse);
    Attr.CreateItem (x, gate, x. pos);
    FixupCondPath (falsePath2, oldMerge2, merge, FALSE);
    FixupCondPath (truePath2, oldMerge, merge2, TRUE);
    FixOldValues (falsePath2);
    IF (oldMerge2 # NIL) THEN
      oldMerge2. Delete()
    END;
    FixupCondPath (merge, NIL, NIL, FALSE);
    CommitIfMerge (merge2)
  END CondAnd;

PROCEDURE Term (region: D.Region; VAR x: Attr.Item);
  VAR
    y: Attr.Item;
    op: SHORTINT;
    pos: LONGINT;
    tempCopy: D.Instruction;
  BEGIN
    Factor (region, x);
    WHILE (S.times <= S.sym) & (S.sym <= S.and) DO
      pos := S.currSymPos;
      IF (S.sym = S.and) THEN            (* conditional and *)
        S.GetSym;
        CondAnd (region, x, NIL, FALSE)
      ELSE                               (* multiplication operators *)
        op := S.sym;
        S.GetSym;
        tempCopy := InsertTempCopy (region, x);
        Factor (region, y);
        QueryTempCopy (x, tempCopy, 1);
        CASE op OF
        | S.times, S.slash:              (* * or / on numeric values or sets *)
          EvalDyadicOp (region, x, y, Opc.classMult-S.times+op, pos, 
                        {},
                        {D.grpNumeric+D.grpOffset, D.grpSet+D.grpOffset})
        | S.div, S.mod:                  (* DIV or MOD on integer values *)
          EvalDyadicOp (region, x, y, Opc.classDivInt-S.div+op, pos, 
                        {},
                        {D.grpInteger+D.grpOffset})
        END
      END;
      x. designator := FALSE
    END
  END Term;

PROCEDURE CondOr (region: D.Region; VAR x: Attr.Item; rhs: D.Usable; negate: BOOLEAN);
  VAR
    y: Attr.Item;
    dummy: SHORTINT;  
    gate: D.Gate;  
    switched: BOOLEAN;
    merge, merge2, oldMerge, oldMerge2: D.Merge; 
    truePath, falsePath, truePath2, falsePath2: D.Region;
  BEGIN
    dummy := CheckOperandType (x, {D.strBoolean}, {});
    switched := SwitchMergeOpnds (x. currValue, 0);
    SplitIfPaths (region, x, truePath, falsePath, merge);
    merge. opcode := Opc.mergeCond;
    ResetVariables (merge, falsePath);
    IF (rhs = NIL) THEN
      IF x. nonlocalExit THEN
        Expr (falsePath, y)
      ELSE
        Term (falsePath, y)
      END;
      dummy := CheckOperandType (y, {D.strBoolean}, {})
    ELSE
      Attr.InitItem (y, x. pos);
      y. type := D.struct[D.strBoolean];
      y. currValue := rhs;
      IF (rhs IS D.Instruction) & 
         (D.instrGuardFor IN rhs(D.Instruction). flags) THEN
        (* move the comparison at the end of a FOR loop into the FALSE guard *)
        falsePath. MoveInstruction (rhs(D.Instruction))
      END
    END;
    IF negate THEN
      EvalMonadicOp (truePath, y, Opc.classNot, y. pos, {D.strBoolean}, {})
    END;
    
    SplitPaths (falsePath, y, truePath2, falsePath2);
    oldMerge2 := truePath2. merge;
    IF switched THEN
      InsertGatePlaceholders (merge. opndList. arg(D.Region));
      merge. opndList. ReplaceOperand (truePath2)
    ELSE
      InsertGatePlaceholders (merge. opndList. nextOpnd. arg(D.Region));
      merge. opndList. nextOpnd. ReplaceOperand (truePath2)
    END;
    truePath2. merge := merge;
    
    merge2 := D.CreateMerge (Opc.mergeCond);
    oldMerge := falsePath2. RegionMerge();
    merge2. Operand (merge);
    merge2. Operand (falsePath2);
    region. Insert (merge2);
    falsePath2. merge := merge2;
    merge. merge := merge2;
    
    gate := merge2. CreateGate (Opc.gate, NIL, D.struct[D.strBoolean]);
    gate. Operand (Sym.constTrue);
    gate. Operand (Sym.constFalse);
    Attr.CreateItem (x, gate, x. pos);
    FixupCondPath (truePath2, oldMerge2, merge, FALSE);
    FixupCondPath (falsePath2, oldMerge, merge2, TRUE);
    FixOldValues (truePath2);
    IF (oldMerge2 # NIL) THEN
      oldMerge2. Delete()
    END;
    FixupCondPath (merge, NIL, NIL, FALSE);
    CommitIfMerge (merge2)
  END CondOr;
  
PROCEDURE SimpleExpr (region: D.Region; VAR x: Attr.Item);
  VAR
    y: Attr.Item;
    op: SHORTINT;
    pos: LONGINT;
    tempCopy: D.Instruction;
    targetType: D.Struct;
  
  PROCEDURE Concat (x, y: D.Const): D.Const;
    CONST
      sizeBuffer = 2*1024;
    VAR
      buffer: ARRAY sizeBuffer OF CHAR;
      b: POINTER TO ARRAY OF CHAR;
      sizeChar: LONGINT;
    
    PROCEDURE Assemble (VAR dest: ARRAY OF CHAR; sizeChar: LONGINT; 
                        form: SHORTINT;
                        VAR src0: ARRAY OF CHAR; len0: LONGINT; 
                        VAR src1: ARRAY OF CHAR; len1: LONGINT): D.Const;
      VAR
        i: LONGINT;
      BEGIN
        FOR i := 0 TO len0*sizeChar-1 DO
          dest[i] := src0[i]
        END;
        FOR i := 0 TO len1*sizeChar-1 DO
          dest[i+len0*sizeChar] := src1[i]
        END;
        RETURN D.GetStringConst (dest, len0+len1, D.struct[form])
      END Assemble;
    
    BEGIN
      ASSERT (x. type = y. type);
      sizeChar := D.struct[x. type. form+(D.strChar8-D.strStringConst8)]. size;
      IF ((x. int+y.int+1)*sizeChar <= sizeBuffer) THEN
        RETURN Assemble (buffer, sizeChar, x. type. form, 
                         x. string^, x. int, y. string^, y. int);
      ELSE  (* only use heap if buffer on stack too small *)
        NEW (b, (x. int+y.int+1)*sizeChar);
        RETURN Assemble (b^, sizeChar, x. type. form,
                         x. string^, x. int, y. string^, y. int)
      END
    END Concat;
  
  BEGIN
    IF (S.sym = S.plus) OR (S.sym = S.minus) THEN
      op := S.sym; pos := S.currSymPos;
      S.GetSym;
      Term (region, x);
      EvalMonadicOp (region, x, Opc.classAdd-S.plus+op, pos, 
                     {},
                     {D.grpNumeric+D.grpOffset, D.grpSet+D.grpOffset});
      x. designator := FALSE
    ELSE
      Term (region, x)
    END;
    WHILE (S.plus <= S.sym) & (S.sym <= S.or) DO
      pos := S.currSymPos;
      IF (S.sym = S.or) THEN             (* conditional or *)
        S.GetSym;
        CondOr (region, x, NIL, FALSE)
      ELSE                               (* addition operations *)
        op := S.sym;
        S.GetSym;
        tempCopy := InsertTempCopy (region, x);
        Term (region, y);
        QueryTempCopy (x, tempCopy, 1);
        IF (op = S.plus) & (x. const # NIL) & ~StdPragmas.conformantMode.true &
           (Sym.TypeInGroup (x. type, D.grpStringConst) OR
            Sym.TypeInGroup (x. type, D.grpChar)) THEN
          (* string concatenation; only available in non-conformant mode *)
          IF (x. type. form = D.strStringConst16) OR
             (y. type. form = D.strStringConst16) OR
             (x. type. form = D.strChar16) OR
             (y. type. form = D.strChar16) THEN
            targetType := D.struct[D.strStringConst16]
          ELSE
            targetType := D.struct[D.strStringConst8]
          END;
          
          IF StringConvertible (y, targetType) &
             StringConvertible (x, targetType) THEN
            (* behold the side effects of the condition's guard ;-) *)
            Attr.CreateItem (x, Concat (x. const, y. const), pos)
          ELSE  (* operand incompatible to type on left side *)
            Sym.ErrT1 (y. pos, 233, x. type)
          END
        ELSE
          EvalDyadicOp (region, x, y, Opc.classAdd-S.plus+op, pos, 
                        {},
                        {D.grpNumeric+D.grpOffset, D.grpSet+D.grpOffset})
        END
      END;
      x. designator := FALSE
    END
  END SimpleExpr;

PROCEDURE Expr* (region: D.Region; VAR x: Attr.Item);
  VAR
    y: Attr.Item;
    op: SHORTINT;
    pos: LONGINT;
    instr: D.Instruction;
    tempCopy: D.Instruction;
  BEGIN
    SimpleExpr (region, x);
    IF (S.eql <= S.sym) & (S.sym <= S.is) THEN
      op := S.sym; 
      pos := S.currSymPos;
      S.GetSym;
      tempCopy := InsertTempCopy (region, x);
      SimpleExpr (region, y);
      QueryTempCopy (x, tempCopy, 1);
      CASE op OF
      | S.eql..S.neq:                    (* equal, not equal *)
        EvalDyadicOp (region, x, y, Opc.classEql-S.eql+op, pos,
                      {D.strBoolean, D.strByte, D.strPtr, D.strNil},
                      {D.grpNumeric+D.grpOffset, D.grpSet+D.grpOffset, 
                       D.grpString8+D.grpOffset, D.grpString16+D.grpOffset,
                       D.grpChar+D.grpOffset, 
                       D.grpPointer+D.grpOffset, D.grpProc+D.grpOffset}) 
      | S.lss..S.geq:                    (* less, greater, etc *)
        EvalDyadicOp (region, x, y, Opc.classEql-S.eql+op, pos,
                      {},
                      {D.grpNumeric+D.grpOffset, D.grpString8+D.grpOffset,
                       D.grpString16+D.grpOffset, D.grpChar+D.grpOffset}) 
      | S.in:                            (* membership test *)
        IF ~Sym.TypeInGroup (y. type, D.grpSet) THEN
          CheckType (y. type, D.grpSet, y. pos);
          Attr.CreateItem (y, D.GetSetConst ({}, D.struct[D.strSet32]), y. pos)
        END;
        BoundSetElement (region, y. type. form, x);
        instr := Attr.DyadicOp (region, 
                       Opc.baseBitTest+D.OperatorSubclass (y. type, 0), 
                       D.struct[D.strBoolean], y, x, pos);
        EvalInstr (x, instr)
      | S.is:                            (* type test *)
        TypeTest (region, x, y, FALSE, pos, x)
      END;
      x. designator := FALSE
    END
  END Expr;

PROCEDURE ConstExpr* (expectedType: SHORTINT): D.Const;
(* pre: `expectedType IN {D.grpChar, D.grpInteger, D.grpAnyType}' *)
  VAR
    x: Attr.Item;
    num: INTEGER;
    form: SHORTINT;
    type: D.Struct;
    dummyRegion: D.GlobalRegion;
  BEGIN
    dummyRegion := Attr.CreateGreg (NIL);
    Expr (dummyRegion, x);
    CheckValue (x);
    Attr.CleanupGreg (dummyRegion);
    
    (* test for constant of expected type *)
    IF (x. const = NIL) OR ~Sym.TypeInGroup (x. type, expectedType) THEN
      CASE expectedType OF
      | D.grpChar: num := 237            (* has to be character constant *)
      | D.grpInteger: num := 209         (* has to be integer constant *)
      | D.grpAnyType: num := 238         (* has to be a constant expression *)
      END;
      E.Err (x. pos, num);
      IF (expectedType = D.grpChar) THEN
        form := D.strChar8
      ELSE
        form := D.strShortInt
      END;
      dummyRegion. Delete();
      RETURN D.GetIntConst (1, D.struct[form])
    ELSE
      dummyRegion. Delete();
      IF Sym.TypeInGroup (x. type, D.grpInteger) THEN
        type := StdTypes.IntType (x. const. int);
        IF (type # x. type) THEN
          (* replace the constant from `x' with one of type `type' *)
          RETURN D.GetIntConst (x. const. int, type)
        END
      ELSIF Sym.TypeInGroup (x. type, D.grpChar) THEN
        type := StdTypes.CharType (x. const. int);
        IF (type # x. type) THEN
          (* replace the constant from `x' with one of type `type' *)
          RETURN D.GetIntConst (x. const. int, type)
        END
      END;
      RETURN x. const
    END
  END ConstExpr;

PROCEDURE Condition* (region: D.Region; VAR x: Attr.Item; negate: BOOLEAN);
(* Parses boolean expression.  An error is signaled if no expression follows
   or it isn't of type BOOLEAN.  *)
  BEGIN
    Expr (region, x);
    CheckValue (x);
    CheckType (x. type, D.strBoolean, x. pos);
    IF negate THEN
      EvalMonadicOp (region, x, Opc.classNot, x. pos, {D.strBoolean}, {})
    END
  END Condition;

PROCEDURE ConditionExit* (region: D.Region; VAR x: Attr.Item;
                          VAR exitInfo: Attr.ExitInfo; 
                          andNeg, condFollows, negateCond, useCond: BOOLEAN);
(* Extended version of `Condition' that takes the variables $exit and $return
   into account.  The generated condition is of the form 
     "[~$return &] [~$exit &] [~$trap &] [condition]"  (if `andNeg=TRUE'), or
     "[$return OR] [$exit OR] [$trap OR] [condition]"  (if `andNeg=FALSE').
   The parameter `andNeg' toggles between the first (TRUE) and the second
   variant (FALSE).  The first three parts are omitted if the corresponding 
   field in `exitInfo' isn't set, no condition is parsed if `condFollows=
   FALSE'.  With `useCond=TRUE' the value of `x' is taken for the condition (it
   is assumed to refer to an instruction).  The condition is negated if 
   `negateCond=TRUE'.  If all fields are FALSE the condition is the value of 
   `andNeg'.  *)
  VAR
    y, inputCond: Attr.Item;
  
  PROCEDURE SetItem (VAR x: Attr.Item; var: D.Object; negate: BOOLEAN);
    BEGIN
      Attr.InitItem (x, S.currSymPos);
      x. obj := var;
      x. type := var. type;
      x. currValue := var. currValue;
      x. nonlocalExit := TRUE;
      IF negate THEN
        EvalMonadicOp (region, x, Opc.classNot, x. pos, {D.strBoolean}, {})
      END
    END SetItem;
  
  PROCEDURE Connect (VAR x: Attr.Item; rhs: D.Usable; negate: BOOLEAN);
    BEGIN
      IF andNeg THEN  
        CondAnd (region, x, rhs, negate)
      ELSE
        CondOr (region, x, rhs, negate)
      END
    END Connect;
  
  BEGIN
    IF exitInfo. exited OR exitInfo. returned OR exitInfo. trapped THEN
      inputCond := x;
      IF exitInfo. returned THEN
        SetItem (x, exitInfo. return, andNeg);
        x. nonlocalExit := TRUE
      ELSE
        Attr.InitItem (x, S.currSymPos)
      END;
      IF exitInfo. exited THEN
        SetItem (y, exitInfo. exit, andNeg);
        IF (x. currValue = NIL) THEN
          x := y
        ELSE
          Connect (x, y. currValue, FALSE);
          x. nonlocalExit := TRUE
        END
      END;
      IF exitInfo. trapped THEN
        SetItem (y, exitInfo. trap, andNeg);
        IF (x. currValue = NIL) THEN
          x := y
        ELSE
          Connect (x, y. currValue, FALSE);
          x. nonlocalExit := TRUE
        END
      END;
      IF condFollows THEN
        Connect (x, NIL, negateCond)
      ELSIF useCond THEN
        (* signal CondOr and CondAnd to move `inputCond. currValue' into
           the false path of the current condition *)
        INCL (inputCond. currValue(D.Instruction). flags, D.instrGuardFor);
        Connect (x, inputCond. currValue, negateCond);
        EXCL (inputCond. currValue(D.Instruction). flags, D.instrGuardFor)
      END
    ELSIF condFollows THEN 
      Condition (region, x, negateCond)
    ELSIF ~useCond THEN
      SetItem (x, exitInfo. exit, andNeg)
    END
  END ConditionExit;

BEGIN
  ProcedureCall := NIL;
  FixupCondPath := NIL;
  CommitIfMerge := NIL;
  AssignToVar := NIL;
  ReclaimFromMem := NIL;
END ParseExpr.
