(* 	$Id: Attributes.Mod,v 1.67 2000/12/26 16:16:56 ooc-devel Exp $	 *)
MODULE Attributes;
(*  Calculation and maintenance of attributes needed by the parser.
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
  S := Scanner, E := Error, D := Data, StdTypes, StdPragmas, 
  Sym := SymbolTable, Opc := Opcode;


TYPE
  (* The parsing procedures for expressions and designators create and operate
     on records of type `Item'.  *)
  Item* = RECORD
    pos*: LONGINT;                        
    (* source position corresponding to this item *)
    obj*: D.Object;
    (* if the designator is a constant, a type, a variable, or a procedure,
       then the reference to the symbol table entry is stored in `obj'; since
       a type cast retains this reference, testing for designators should use
       the boolean field `designator' below *)
    type*: D.Struct;
    (* type structure associated with this item *)
    const*: D.Const;
    (* a constant value used as factor, or the value of a constant object *)
    currValue*: D.Usable;
    (* r-value of the item; this is either a constant, or a reference to the 
       result that defined the current value (or NIL for types) *)
    baseValue*: D.Usable;
    (* r-value of the variable in field `assignment' that started the
       designator, or the r-value of the last access-heap operation in
       the designator *)
    basePos*: LONGINT;
    (* the file position the designator is starting at *)
    adr*: D.Usable;
    (* l-value of the item; this is an _write_only_ field, to get the item's 
       address call the tb proc `Adr';  if `Adr()' is NIL, then the value isn't
       associated with any address (like some constants or type references) *)
    ttHint*: D.Usable;
    (* hint to the value of the type tag or length information, set by 
       `Designator'; the parameter object if the designator accesses a variable
       record parameter or an open array parameter, an address for pointers *)
    assignment*: D.Addressable;
    (* here `Designator' stores the variable (`D.Object') or heap object 
       (`D.Struct') that would be modified when assigning to this item; this
       is either a variable or the type most recent pointer deref operation;
       in the latter case it is the type of the heap object being accessed *)
    nonlocalExit*: BOOLEAN;
    (* this is set if the item represents a nonlocal exit condition (ie, $exit,
       $return, or a combination of both) *)
    designator*: BOOLEAN;
    (* TRUE if the item describes a designator, i.e., is derived from a 
       variable instead of an expression *)
    arrayDim*: INTEGER;
    (* this is the number of the array's current dimension relative to the
       object in `assignment'; for an array without any indices this is 0 *)
    readOnlyPos*: LONGINT;
    (* position of the variable or the field that made this designator read 
       only, `S.undefPos' otherwise; for open array value parameters that
       have no local copy of the value (happens with C interface code), 
       the position value is negative *)
  END;

TYPE
  (* This record keeps information about nonlocal exits in a procedure's or
     the module's body (ie, about EXIT and RETURN statement).  *)
  ExitInfo* = RECORD
    result*: D.Object;
    return*: D.Object;
    returned*: BOOLEAN;
    exit*: D.Object;
    exited*: BOOLEAN;
    trap*: D.Object;
    trapped*: BOOLEAN;
  END;
     

PROCEDURE InitItem* (VAR x: Item; pos: LONGINT);
  BEGIN
    x. pos := pos;
    x. obj := NIL;
    x. type := NIL;
    x. const := NIL;
    x. adr := NIL;
    x. currValue := NIL;
    x. baseValue := NIL;
    x. basePos := -1;
    x. ttHint := NIL;
    x. assignment := NIL;
    x. nonlocalExit := FALSE;
    x. designator := TRUE;
    x. arrayDim := 0;
    x. readOnlyPos := D.undefPos
  END InitItem;

PROCEDURE CreateItem* (VAR x: Item; u: D.Usable; pos: LONGINT);
(* Creates an item corresponding to the instruction or a constant `u'.
   pre: (u IS D.Result) OR (u IS D.Const) OR (u IS D.Struct) *)
  BEGIN
    InitItem (x, pos);
    WITH u: D.Const DO
      x. type := u. type;
      x. const := u;
      x. currValue := u
    | u: D.Result DO
      x. type := u. type;
      x. currValue := u
    | u: D.Struct DO
      x. type := u
    END
  END CreateItem;

PROCEDURE SetOpndPos* (instr: D.Instruction; pos: LONGINT);
(* Sets the file position of the last operand of `instr' to `pos'.  *)
  VAR
    opnd: D.Opnd;
  BEGIN
    opnd := instr. LastOperand();
    opnd. pos := pos
  END SetOpndPos;

PROCEDURE Operand* (instr: D.Instruction; VAR x: Item);
(* Appends `x' to the operand list of instruction `instr'.  *)
  BEGIN
    instr. Operand (x. currValue);
    SetOpndPos (instr, x. pos)
  END Operand;

PROCEDURE DyadicOp* (region: D.Region; opcode: INTEGER; type: D.Struct; 
                     VAR opnd1, opnd2: Item; pos: LONGINT): D.Instruction;
  VAR
    instr: D.Instruction;
  BEGIN
    instr := region. CreateInstruction (opcode, type, pos);
    Operand (instr, opnd1);
    Operand (instr, opnd2);
    RETURN instr
  END DyadicOp;


PROCEDURE InitExitInfo* (VAR i: ExitInfo);
  BEGIN
    i. result := NIL;
    i. return := NIL;
    i. returned := FALSE;
    i. exit := NIL;
    i. exited := FALSE;
    i. trap := NIL;
    i. trapped := FALSE
  END InitExitInfo;

PROCEDURE ExitInfoOr* (VAR exitInfo, nestedInfo: ExitInfo);
  BEGIN
    exitInfo. returned := exitInfo. returned OR nestedInfo. returned;
    exitInfo. exited := exitInfo. exited OR nestedInfo. exited;
    exitInfo. trapped := exitInfo. trapped OR nestedInfo. trapped
  END ExitInfoOr;

PROCEDURE CreateGuard* (VAR cond: Item; opcode: INTEGER; pos: LONGINT): D.Guard;
  VAR
    guard: D.Guard;
  BEGIN
    guard := D.CreateGuard (cond. currValue, opcode, pos);
    guard. opndList. pos := cond. pos;
    RETURN guard
  END CreateGuard;

PROCEDURE CreateGreg* (bodyOf: D.Object): D.GlobalRegion;
  VAR
    greg: D.GlobalRegion;
  BEGIN
    NEW (greg);
    D.InitGuard (greg, Sym.constTrue, Opc.guardGreg, S.currSymPos);
    greg. bodyOf := bodyOf;
    greg. enter := greg. CreateInstruction (Opc.enter, NIL, S.currSymPos);
    greg. exit := greg. CreateInstruction (Opc.exit, NIL, S.currSymPos);
    RETURN greg
  END CreateGreg;

PROCEDURE InitGreg* (greg: D.GlobalRegion; VAR i: ExitInfo): D.GlobalRegion;
(* Creates top level region for procedure or module `bodyOf'.  The receiver and
   formal parameters are inserted as results into the enter instruction.  The
   enter and exit instructions are the first and second element in the 
   instruction list `grep. instrList'.  *)
  VAR 
    bodyOf, param: D.Object;
    
  PROCEDURE Parameter (obj: D.Object);
    VAR
      i: INTEGER;
      res: D.Result;
    BEGIN
      (* formal parameter *)
      obj. currValue := greg. enter. AppendResult (D.CreateSymLocation (obj, D.symLocObject), obj. type);
      (* address parameter *)
      IF StdTypes.PassPerReference (obj, TRUE) THEN
        res := greg. enter. AppendResult (D.CreateSymLocation (obj, 
                               D.symLocAddress), D.struct[D.strAddress])
      END;
      IF (obj. mode = D.objVarPar) & (obj. type. form = D.strRecord) THEN  
        (* type tag *)
        IF ~(D.objNoTypeTag IN obj. flags) THEN
          res := greg. enter. AppendResult (D.CreateSymLocation (obj, 
                                                         D.symLocTypeTag), NIL)
        END
      ELSE                               (* open array length info *)
        IF ~(D.objNoLengthTag IN obj. flags) THEN
          FOR i := 1 TO obj. type. OpenDimensions() DO
            res := greg. enter. AppendResult (D.CreateSymLocation (obj, i-1), D.struct[D.strLongInt])
          END
        END
      END
    END Parameter;
  
  PROCEDURE CreateFalse(): D.Instruction;
    VAR
      instr: D.Instruction;
    BEGIN
      instr := greg. CreateInstruction (Opc.copy, D.struct[D.strBoolean], D.undefPos);
      instr. Operand (Sym.constFalse);
      RETURN instr
    END CreateFalse;
  
  BEGIN
    InitExitInfo (i);
    bodyOf := greg. bodyOf;
    (* provide initial value for $store variable *)
    Sym.store. currValue := greg. CreateInstruction (Opc.createStore, D.struct[D.strUndef], D.undefPos);
    INCL (Sym.store. currValue(D.Instruction). flags, D.instrIsDisabled);
    Sym.store. localTo := bodyOf;                                             
    (* create variable that holds the `return' flag *)
    i. return := Sym.NewObject ("$return", D.objVar, bodyOf. pos);
    i. return. type := D.struct[D.strBoolean];
    i. return. localTo := bodyOf;
    i. return. currValue := CreateFalse();
    i. trap := Sym.NewObject ("$trap", D.objVar, bodyOf. pos);
    i. trap. type := D.struct[D.strBoolean];
    i. trap. localTo := bodyOf;
    i. trap. currValue := CreateFalse();
    (* add receiver as result to enter instruction *)
    IF (bodyOf. mode = D.objTBProc) THEN
      Parameter (bodyOf. data(D.Object))
    END;
    IF (bodyOf. mode # D.objModule) THEN
      IF (bodyOf. type. base. form # D.strNone) THEN
        (* create variable to keep function result, add it as 
           operand to exit *)
        i. result := Sym.NewObject ("$result", D.objVar, bodyOf. pos);
        i. result. type := bodyOf. type. base;
        i. result. localTo := bodyOf;
        greg. exit. Operand (i. result);
        greg. exit. opndList. location := D.CreateSymLocation (i. result, D.symLocObject)
      END;
      (* add formal parameters as results to enter instruction *)
      param := bodyOf. type. decl;
      WHILE (param # NIL) DO
        Parameter (param);
        param := param. rightObj
      END
    END;
    RETURN greg
  END InitGreg;

PROCEDURE TracesToEmptyStore* (var: D.Object; store: D.Usable): BOOLEAN;
(* Given a variable and a value of $store, determine if there exists a path
   through $store that doesn't write to this variable.  In other words, return
   TRUE if the value in `store' can be the result of a `create-store' 
   instruction.  *)
  VAR
    opnd: D.Opnd;
    r: D.Usable;
    i: D.Instruction;
    
  PROCEDURE ModifiedVarParam (var: D.Object; call: D.Instruction): BOOLEAN;
  (* Returns TRUE iff the procedure call instruction takes `var' as a variable
     parameter.  *)
    VAR
      opnd: D.Opnd;
      param: D.Object;
    BEGIN
      opnd := call. opndList;
      WHILE (opnd # NIL) DO
        IF (opnd. location # NIL) &
           (opnd. location(D.SymLocation). var IS D.Object) THEN
          param := opnd. location(D.SymLocation). var(D.Object);
          IF (param. mode = D.objVarPar) & 
             (opnd. arg IS D.Instruction) & 
             ((opnd. arg(D.Instruction). opcode = Opc.accessNonlocal) OR 
              (opnd. arg(D.Instruction). opcode = Opc.accessVarParam)) &
             (opnd. arg(D.Instruction). opndList. arg = var) THEN 
            RETURN TRUE
          END
        END;
        opnd := opnd. nextOpnd
      END;
      RETURN FALSE
    END ModifiedVarParam;
  
  BEGIN
    r := store;
    WITH r: D.Result DO
      i := r. instr;          (* `i' is the instruction that defines `store' *)
      IF (i. opcode = Opc.createStore) THEN 
        RETURN TRUE
      
      ELSIF (i. opcode = Opc.call) THEN
        (* value is set by a side-effect of a procedure call *)
        IF (i. GetResult (var, D.symLocObject) # NIL) OR
           ModifiedVarParam (var, i) THEN
          RETURN FALSE
        ELSE  (* get $store from call, continue trace *)
          opnd := i. GetOperand (Sym.store, D.symLocObject);
          (* since the call writes to $store it also has an operand for it;
             that is, `opnd' should never be NIL here *)
          RETURN TracesToEmptyStore (var, opnd. arg)
        END
        
      ELSIF (i. opndList. arg = var) &
            ((var.mode = D.objVarPar) & (i. opcode = Opc.updateVarParam) OR
             (var.mode # D.objVarPar) & (i. opcode = Opc.updateNonlocal)) THEN 
        (* value is defined by a previous update on the same variable *)
        RETURN FALSE
        
      ELSIF (i. opcode = Opc.gate) & (i. region. opcode = Opc.mergeLoop) THEN
        (* trace only through the second operand of a loop gate *)
        RETURN TracesToEmptyStore (var, i. opndList. nextOpnd. arg)
        
      ELSIF (i. opcode = Opc.updateHeap) OR
            (i. opcode = Opc.updateNonlocal) OR
            (i. opcode = Opc.updateVarParam) THEN
        (* trace through third operand of an update-heap, update-nonlocal, or
           update-var-param instruction *)
        RETURN TracesToEmptyStore (var, i. opndList. nextOpnd. nextOpnd. arg)
        
      ELSIF (i. opcode = Opc.gate) THEN
        (* see if any gate operand can be traced to create-store *)
        opnd := i. opndList. nextOpnd;
        WHILE (opnd # NIL) DO
          IF TracesToEmptyStore (var, opnd. arg) THEN
            RETURN TRUE
          END;
          opnd := opnd. nextOpnd
        END;
        RETURN FALSE
        
      ELSE
        RETURN FALSE
      END
    ELSE
      RETURN FALSE
    END
  END TracesToEmptyStore;

PROCEDURE GuardExit* (greg: D.GlobalRegion; VAR exitInfo: ExitInfo);
(* Guards exit instruction against $trap and $return=FALSE.  *)
  VAR
    region: D.Region;
    instr: D.Instruction;
    guard: D.Guard;
  BEGIN
    region := greg;
    (* guard exit instruction against $trap *)
    IF ~(exitInfo. trap. currValue IS D.Instruction) OR
       (exitInfo. trap. currValue(D.Instruction). opcode # Opc.copy) OR
       (exitInfo. trap. currValue(D.Instruction). opndList. arg # Sym.constFalse) THEN
      guard := D.CreateGuard (exitInfo. trap. currValue, Opc.guardFalse, S.currSymPos);
      region. Insert (guard);
      guard. MoveInstruction (greg. exit);
      region := guard
    END;
    IF (exitInfo. result # NIL) THEN
      (* move exit into guard against TRUE *)
      guard := D.CreateGuard (exitInfo. return. currValue, Opc.guardTrue, S.currSymPos);
      region. Insert (guard);
      guard. MoveInstruction (greg. exit);
      (* create trap in FALSE guard *)
      guard := D.CreateGuard (exitInfo. return. currValue, Opc.guardFalse, S.currSymPos);
      region. Insert (guard);
      instr := guard. CreateInstruction (Opc.trapReturn, NIL, S.currSymPos);
      IF ~StdPragmas.functResult. true THEN
        INCL (instr. flags, D.instrIsDisabled)
      END;
      INCL (instr. flags, D.instrNotDead)
    END
  END GuardExit;

PROCEDURE UnguardExit* (greg: D.GlobalRegion; VAR exitInfo: ExitInfo);
(* Undo changes of `GuardExit' by moving the "exit" instruction to the top
   level.  This is intended to avoid problems if "exit" ends up in a region
   that is unreachable, and consequently optimised away.  *)
  BEGIN
    IF (greg. exit. region # greg) THEN
      greg. MoveInstruction (greg. exit)
    END
  END UnguardExit;


PROCEDURE FindAddEnterResult* (region: D.Region; var: D.Addressable; 
                               attrib: INTEGER; type: D.Struct): D.Result;
(* Searches for (var, attrib) in the local enter instruction.  If no such
   result exists, it is appended to the result list.  *)
  VAR
    res: D.Result;
    enter: D.Instruction;
  BEGIN
    enter := region. EnterInstr();
    res := enter. GetResult (var, attrib);
    IF (res = NIL) THEN
      res := enter. AppendResult (D.CreateSymLocation (var, attrib), type)
    END;
    RETURN res
  END FindAddEnterResult;


PROCEDURE Address* (region: D.Region; var: D.Addressable; 
                    pos: LONGINT): D.Result;
  BEGIN
    IF (var IS D.Object) & 
       ((var(D.Object). mode = D.objVarPar) OR
        ((var(D.Object). mode = D.objVar) &
         (var(D.Object). localTo # Sym.currScope))) THEN
      RETURN FindAddEnterResult (region, var, D.symLocAddress, 
                                      D.struct[D.strAddress])
    ELSE
      RETURN region. CreateAdrInstr (var, pos);
    END
  END Address;

PROCEDURE TBProcAdr* (region: D.Region; typeTag: D.Usable; 
                      staticType: D.Struct;
                      tbProc: D.Object; pos: LONGINT;
                      staticCall: BOOLEAN): D.Usable;
  VAR
    instr: D.Instruction;
  BEGIN
    IF staticCall THEN
      RETURN region. CreateAdrInstr (tbProc, pos)
    ELSE
      instr := region. CreateInstruction (Opc.tbProcAdr, 
                                          D.struct[D.strAddress], pos);
      instr. Operand (typeTag);
      instr. Operand (staticType);
      instr. Operand (tbProc);
      RETURN instr
    END
  END TBProcAdr;

PROCEDURE Adr* (region: D.Region; VAR x: Item): D.Usable;
  BEGIN
    IF (x. adr = NIL) THEN
      IF (x. const # NIL) & Sym.TypeInGroup (x. type, D.grpStringConst) THEN
        x. adr := region. CreateAdrInstr (x. const, x. pos)
      ELSIF (x. obj # NIL) & (x. obj. mode IN {D.objVar, D.objVarPar}) THEN
        x. adr := Address (region, x. obj, x. pos)
      END
    END;
    IF (x. adr = NIL) THEN
      (* make sure that the value NIL is never returned; otherwise the
         compiler will break when attempting to use NIL as argument of 
         a GSA instruction *)
      RETURN D.constUndef
    ELSE
      RETURN x. adr
    END
  END Adr;

PROCEDURE TypeTag* (region: D.Region; VAR x: Item; base: INTEGER): D.Usable;
(* Retrieves type tag, i.e. the type descriptor's address, of designator `x'.
   `base=-1' uses the dynamic type as base, `base=0' the static type, and
   `base=1' the static type's base type.  
   Emits an error if the type or variable does not have a associated 
   type descriptor.  *)
  VAR
    instr: D.Instruction;
    type: D.Struct;
  
  PROCEDURE TypeDescrAdr (type: D.Struct): D.Usable;
    BEGIN
      IF (D.structNoDescriptor IN type. flags) THEN
        E.Err (x. pos, 281)              (* this type has no descriptor *)
      END;
      RETURN region. CreateAdrInstr (type, x. pos)
    END TypeDescrAdr;
  
  BEGIN
    IF (x. ttHint # NIL) & (base < 0) THEN
      IF (x. ttHint IS D.Object) & 
         (x. ttHint(D.Object). mode = D.objVarPar) THEN
        (* `x' is a variable parameter of type record, its type tag is passed
           as an implicit procedure parameter *)
        RETURN FindAddEnterResult (region, x. ttHint(D.Object), 
                                   D.symLocTypeTag, NIL)
      ELSE                               (* `x' is (or was) a pointer *)
        IF (D.structStaticPointer IN x. type. flags) THEN  
          (* `x' is a pointer without type tag, so return its static type *)
          RETURN TypeDescrAdr (x. type. base)
        ELSE
          instr := region. CreateInstruction (Opc.typeTag, NIL, x. pos);
          IF StdPragmas.derefCheck. true THEN
            (* note: dead code elimination will remove this instruction if it
                     is never used, even if it may raise an exception *)
            INCL (instr. flags, D.instrCheckNil)
          END;
          instr. Operand (x. ttHint);
          SetOpndPos (instr, x. pos);
          RETURN instr
        END
      END
    ELSE  (* `x' is a static record and hasn't a dynamic type *)
      IF (x. type. form = D.strPointer) THEN
        type := x. type. base
      ELSE
        type := x. type
      END;
      IF (base <= 0) OR (type. base = NIL) THEN
        RETURN TypeDescrAdr (type)
      ELSE
        RETURN TypeDescrAdr (type. base)
      END
    END
  END TypeTag;

PROCEDURE HasLengthInfo* (VAR array: Item; dim: INTEGER): BOOLEAN;
(* Returns FALSE if there is no length information available for the dimension
   `dim' of `array'.  *)
  VAR
    d: INTEGER;
    t: D.Struct;
  BEGIN
    t := array. type;
    IF ~Sym.TypeInGroup (t, D.grpStringConst) THEN
      IF (array. arrayDim+dim = 0) & (array. obj # NIL) & 
         (D.objIsParameter IN array. obj. flags) &
         (D.objNoLengthTag IN array. obj. flags) THEN
        RETURN FALSE
      ELSE
        d := dim;
        WHILE (d # 0) & Sym.TypeInGroup (t, D.grpArray) DO
          DEC (d);
          t := t. base
        END;
        IF (t. form = D.strOpenArray) & 
           (D.structNoLengthInfo IN t. flags) THEN
          RETURN FALSE
        END
      END
    END;
    RETURN TRUE
  END HasLengthInfo;

PROCEDURE ArrayLength* (region: D.Region; VAR array: Item; dim: INTEGER; 
                        pos: LONGINT; adaptType: BOOLEAN; VAR result: Item);
(* Return length of item `array' in dimension `dim'.  `pos' is the file 
   position that should be associated with the calculations.  `array' has to be
   an array variable or a string constant.  `dim' is interpreted relative to
   the designators implizit dimension, _not_ as an absolute dimension index of 
   the variable's array type.  Emits an error if no length data is available 
   for the requested array dimension.
   pre: `dim' is not negative
   result: The expression or constant that represents the array length, or
     the constant 1 if `array' isn't an array designator or `dim' denotes an 
     invalid dimension.  If `adaptType' is TRUE, and the result is a constant
     value, then the result's type is the smallest fitting integer type, 
     otherwise the type is LONGINT.  *)
  VAR
    t: D.Struct;
    len: D.Usable;
    d: INTEGER;
  
  PROCEDURE GetConst (value: LONGINT): D.Const;
    BEGIN
      IF adaptType THEN
        RETURN D.GetIntConst (value, StdTypes.IntType (value))
      ELSE
        RETURN D.GetIntConst (value, D.struct[D.strLongInt])
      END
    END GetConst;
  
  BEGIN
    IF ~HasLengthInfo (array, dim) THEN
      E.Err (array. pos, 280);           (* no info available on length *)
      len := GetConst (1)
    ELSE
      t := array. type;
      IF Sym.TypeInGroup (t, D.grpStringConst) THEN
        (* item denotes a string constant; length is string length plus 1 *)
        len := GetConst (array. const. int+1)
      ELSE
        (* unroll type of array to the desired dimension *)
        d := dim;
        WHILE (d # 0) & Sym.TypeInGroup (t, D.grpArray) DO
          DEC (d);
          t := t. base
        END;
        IF Sym.TypeInGroup (t, D.grpArray) THEN (* valid dimension *)
          IF (t. form = D.strArray) THEN     (* fixed size array *)
            len := GetConst (t. len)
          ELSIF (array. assignment IS D.Object) THEN (* open array parameter *)
            len := FindAddEnterResult (region, array. ttHint(D.Object), 
                                       array. arrayDim+dim, D.struct[D.strLongInt])
          ELSE                               (* open array pointer base type *)
            len := region. CreateDyadicOp (Opc.arrayLength, D.struct[D.strLongInt], array. ttHint, D.GetIntConst (array. arrayDim+dim, D.struct[D.strInteger]), pos);
            IF StdPragmas.derefCheck. true THEN
              (* note: dead code elimination will remove this instruction if it
                       is never used, even if it may raise an exception *)
              INCL (len(D.Instruction). flags, D.instrCheckNil)
            END
          END
        ELSE                                 (* invalid dimension number *)
          len := GetConst (1)
        END
      END
    END;
    CreateItem (result, len, pos)
  END ArrayLength;

PROCEDURE SizeOfItem* (region: D.Region; VAR x: Item; dim: INTEGER; 
                       pos: LONGINT; VAR size: Item);
(* Calculates the size of the variable denoted by the designator `x'.  The 
   parameter `dim' can be used to select between the size of the whole variable
   (`dim=0') or the size of array elements.  In the latter case any positive 
   value of `dim' denotes the size of the `dim's element type of `x'.
   pre: (x. type. form IN D.arrayTypes) & (dim >= 0) OR (dim = 0); the maximum
     value of `dim' is the number of dimensions of `x. type'.  
   result: The size of the variable evaluating to LONGINT.  *)
  VAR
    i: INTEGER;
    t: D.Struct;
    product: D.Usable;
  
  PROCEDURE Mult (opnd0, opnd1: D.Usable): D.Usable;
    BEGIN
      RETURN region. CreateDyadicOp (Opc.multl, D.struct[D.strLongInt], opnd0, opnd1, pos)
    END Mult;
  
  BEGIN
    (* select array element *)
    i := 0;
    t := x. type;
    WHILE (i # dim) DO
      INC (i);
      t := t. base
    END;
    IF (t. size >= 0) THEN               (* fixed size type *)
      product := D.GetIntConst (t. size, D.struct[D.strLongInt])
    ELSIF (t. form = D.strStringConst8) THEN
      (* item denotes a string constant; size is string length plus 1 *)
      product := D.GetIntConst (x. const. int+1, D.struct[D.strLongInt])
    ELSIF (t. form = D.strStringConst16) THEN
      (* item denotes a string constant; size is string length plus 1 times
         SIZE(LONGCHAR) *)
      product := D.GetIntConst ((x. const. int+1)*D.struct[D.strChar16]. size,
                                D.struct[D.strLongInt])
    ELSE                                 (* open array variable *)
      ArrayLength (region, x, dim, pos, FALSE, size);
      product := size. currValue;
      t := t. base;
      INC (dim);
      WHILE (t. form = D.strOpenArray) DO
        ArrayLength (region, x, dim, pos, FALSE, size);
        product := Mult (product, size. currValue);
        t := t. base;
        INC (dim)
      END;
      product := Mult (product, D.GetIntConst (t.size, D.struct[D.strLongInt]))
    END;
    CreateItem (size, product, x. pos)
  END SizeOfItem;

PROCEDURE GetNonParamOpnd* (call: D.Instruction): D.Opnd;
(* Retrieve the first operand of the call instruction that doesn't correspond
   to one of the formal parameters of the called procedure, but rather to
   a nonlocal variable access.  *)
  VAR
    opnd: D.Opnd;
    receiver, param: D.Object;
  
  PROCEDURE OpndCount (formal: D.Object): INTEGER;
    VAR
      n: INTEGER;
    BEGIN
      n := 1;
      IF StdTypes.PassPerReference (formal, TRUE) THEN  (* address *)
        INC (n)
      END;
      IF (formal. mode = D.objVarPar) & 
         (formal. type. form = D.strRecord) THEN  (* type tag *)
        IF ~(D.objNoTypeTag IN formal. flags) THEN
          INC (n)
        END
      ELSIF (formal. type. form = D.strOpenArray) &
            (formal. type. base. form = D.strByte) THEN
        (* formal parameter is an ARRAY OF BYTE: size in bytes *)
        IF ~(D.objNoLengthTag IN formal. flags) THEN
          INC (n)
        END
      ELSIF ~(D.objNoLengthTag IN formal. flags) THEN
        (* open array length info *)
        INC (n, formal. type. OpenDimensions())
      END;
      RETURN n
    END OpndCount;
  
  PROCEDURE SkipOpnds (n: INTEGER; opndList: D.Opnd): D.Opnd;
    BEGIN
      WHILE (n # 0) DO
        opndList := opndList. nextOpnd;
        DEC (n)
      END;
      RETURN opndList
    END SkipOpnds;
  
  BEGIN
    opnd := call. NthOperand (3);
    
    receiver := call. GetReceiver();
    IF (receiver # NIL) THEN
      opnd := SkipOpnds (OpndCount (receiver), opnd)
    END;
    
    param := call. opndList. nextOpnd. arg(D.Struct). decl;
    WHILE (param # NIL) DO
      IF (param. mode = D.objRestParam) THEN
        WHILE (opnd # NIL) & (opnd. arg # Sym.store) & (opnd. arg # Sym.mem) DO
          opnd := opnd. nextOpnd
        END
      ELSE
        opnd := SkipOpnds (OpndCount (param), opnd);
      END;
      param := param. rightObj
    END;
    
    RETURN opnd
  END GetNonParamOpnd;

PROCEDURE PartOfStore* (proc: D.Object; loc: D.Location): BOOLEAN;
(* Result is TRUE iff the object referred to by `loc' is part of $store as 
   seen from procedure `proc'.  Note that the classification explicitly depends
   on the procedure, i.e., different procedures have different $stores.  For
   $mem and $store result is always FALSE.  *)
  VAR
    var: D.Addressable;
  BEGIN
    IF (loc = NIL) OR (loc(D.SymLocation). attrib # D.symLocObject) THEN
      RETURN FALSE
    ELSE
      var := loc(D.SymLocation). var;
      RETURN (var # Sym.store) & 
             (var # Sym.mem) &
             ((var IS D.Struct) OR
              (var IS D.Object) & (var(D.Object).localTo # proc))
    END
  END PartOfStore;


PROCEDURE ContainsRuntimeCheck* (region: D.Region);
(* Marks greg's enter instruction with `D.instrNotDead'.
   Called whenever a run-time check is inserted into `region'.  *)
  BEGIN
    WHILE (region. region # NIL) DO
      region := region. region
    END;
    WITH region: D.GlobalRegion DO
      IF (region. enter # NIL) THEN
        INCL (region. enter. flags, D.instrNotDead)
      END
    ELSE
    END
  END ContainsRuntimeCheck;

PROCEDURE CleanupGreg* (greg: D.GlobalRegion);
(* Resets the current values of nonlocal objects that are modified in the
   current global region.  Removes delete-store instruction.  Resets $reg.
   And some more.  *)
  VAR
    instr, access, exit: D.Instruction;
    opnd: D.Opnd;
    var: D.Addressable;
    obj: D.Object;
    res, nextResult: D.Result;
  
  PROCEDURE ScanUpdates (obj: D.Object);
    VAR
      obj2: D.Object;
    BEGIN
      IF (obj # NIL) THEN
        ScanUpdates (obj. leftObj);
        ScanUpdates (obj. rightObj);
        IF (D.objIsParameter IN obj. flags) THEN
          obj2 := obj. data(D.Object);
          IF (obj2. currValue # obj2) &
             ~((obj2. currValue IS D.Result) &
               (obj2. currValue(D.Result). instr. opcode = Opc.enter)) THEN
            INCL (obj2. flags, D.objIsUpdated)
          END
        END
      END
    END ScanUpdates;
  
  PROCEDURE RemoveNoopGateHints (r: D.Region);
    VAR
      instr, next: D.Instruction;
    BEGIN
      instr := r. instrList;
      WHILE (instr # NIL) DO
        next := instr. nextInstr;
        WITH instr: D.Region DO
          RemoveNoopGateHints (instr)
        ELSE
          IF (instr. opcode = Opc.noopGateHint) THEN
            instr. Delete
          END
        END;
        instr := next
      END
    END RemoveNoopGateHints;
  
  BEGIN
    RemoveNoopGateHints (greg);
    
    (* create `delete-store' instruction *)
    instr := greg. CreateInstruction (Opc.deleteStore, NIL, D.undefPos);
    INCL (instr. flags, D.instrNotDead);
    instr. Operand (Sym.store. currValue);
    
    instr := greg. ExitInstr();
    (* provide operands of exit that correspond to variable parameters or to 
       nonlocal variables with their current value at procedure exit *)
    opnd := instr. opndList;
    WHILE (opnd # NIL) DO
      IF (opnd. arg IS D.Object) &
         (opnd. arg(D.Object). name^ # "$result") THEN
        obj := opnd. arg(D.Object);
        IF (obj. mode = D.objVarPar) THEN
          access := greg. CreateInstruction (Opc.accessVarParam, obj. type, instr. pos)
        ELSE
          access := greg. CreateInstruction (Opc.accessNonlocal, obj. type, instr. pos)
        END;
        access. Operand (obj);
        access. Operand (Address (greg, obj, instr. pos));
        access. Operand (Sym. store. currValue);
        opnd. ReplaceOperand (access)
      END;
      opnd := opnd. nextOpnd
    END;
    (* move any $mem operand to end of operand list *)
    opnd := instr. GetOperand (Sym.mem, D.symLocObject);
    IF (opnd # NIL) THEN
      opnd. MoveOperandToEnd()
    END;
    
    (* set `objIsUpdated' for parameters *)
    IF (greg. bodyOf # NIL) THEN
      ScanUpdates (greg. bodyOf. localDecl)
    END;
    
    (* reset `currValue' fields for structs or nonlocal objects to the 
       adressable itself *)
    (* correct operands of exit instruction *)
    opnd := instr. opndList;
    WHILE (opnd # NIL) DO
      var := opnd. location(D.SymLocation). var;
      IF ~(var IS D.Object) OR (var(D.Object). name^ # "$result") THEN
        var. currValue := var
      END;
      opnd := opnd. nextOpnd
    END;

    (* correct results of enter instruction *)
    instr := greg. EnterInstr();
    res := instr. nextResult;
    WHILE (res # NIL) DO
      nextResult := res. nextResult; 
      
      IF (res. location(D.SymLocation). attrib = D.symLocObject) THEN
        var := res. location(D.SymLocation). var;
        IF ~(var IS D.Object) OR (var(D.Object). localTo # greg. bodyOf) THEN
          var. currValue := var
        END
      END;
      
      res := nextResult
    END;
    res := instr. GetResult (Sym.mem, D.symLocObject);
    IF (res # NIL) THEN
      res. MoveResultToEnd()
    END;
    
    (* set the exit instruction's position to the position of the body's END *)
    exit := greg. ExitInstr();
    exit. pos := S.currSymPos
  END CleanupGreg;

END Attributes.
