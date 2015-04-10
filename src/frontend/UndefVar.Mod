(* 	$Id: UndefVar.Mod,v 3.15 1999/05/07 18:29:04 acken Exp $	 *)
MODULE UndefVar;
(*  Detects use of undefined variables and missing function returns.
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
  D := Data, E := Error, S := Scanner, Opc := Opcode, Attr := Attributes, 
  Cond := GuardCond, Sym := SymbolTable;

(* 
What should be detected?
- use of an undefined variable in an instruction
- use of gates that may have an undefined variable as input
- call of a nested procedure that accesses an undefined variable (that is local
  to the calling procedure)
- passing of an undefined variable to a VAR parameter that is or may be read 
  before it is written to (this would need a flag in the symbol table)
Nonlocal exits (EXIT, RETURN, and traps) should be considered when calculating
the flow of undefined values.  To accomplish this this module implements 
very restricted forms of constant forwarding and dead code detection (although
it doesn't modify the GSA code).
A warning is issued when passing an undefined variable to a variable parameter
that is accessed before it's defined, unless the definition of called procedure
follows the call.
This module cannot detect every possible use of an undefined variable with 
absolute precision.  It tries to keep on the safe side and it shouldn't ignore
any such use.  It may emit warnings that can be dismissed upon closer 
inspection.  Time will show how reliable the used heuristics are...
*)

CONST
  undefined = 0;
  maybeUndefined = 1;
  notInspected = 1;
  inspected = -1;
  
TYPE
  InfoList = POINTER TO ARRAY OF Cond.RegionInfo;
  CondList = POINTER TO ARRAY OF Cond.Condition;
  
VAR
  infoList: InfoList;
  trueList: CondList;
  topOfStack: INTEGER;

TYPE
  UseStack = POINTER TO ARRAY OF D.Opnd;

VAR
  useStack: UseStack;
  useStackSize: LONGINT;
  
  
PROCEDURE AddToTrue (VAR c: Cond.Condition);
(* Add `c' to the list of conditions in `trueList' that are known to hold.
   Change the marker of the condition's value in such a way that its
   absolute value is the index of `c' in `trueList'.  *)
  VAR
    j: INTEGER;
    newList: CondList;
  BEGIN
    IF (c. value IS D.Result) THEN
      c. value(D.Result). marker := c. value(D.Result). marker*topOfStack;
      IF (topOfStack = LEN (trueList^)) THEN
        NEW (newList, topOfStack+128);
        FOR j := 0 TO topOfStack-1 DO
          newList[j] := trueList[j]
        END;
        trueList := newList
      END;
      trueList[topOfStack] := c;
      INC (topOfStack)
    END
  END AddToTrue;

PROCEDURE False (VAR c: Cond.Condition): BOOLEAN;
  VAR
    i: INTEGER;
  BEGIN
    i := 2;
    FOR i := 2 TO topOfStack-1 DO
      IF (Cond.Implies (trueList[i], c) = Cond.false) THEN
        RETURN TRUE
      END
    END;
    RETURN FALSE
  END False;

PROCEDURE Reachable (var: D.Object; opnd: D.Opnd): BOOLEAN;
(* Returns TRUE iff there exists a possible path of data flow through gates
   that delivers `var' into `opnd'.  *)
  VAR
    dummy: BOOLEAN;
    old: INTEGER;
    
  PROCEDURE AddGuardToTrue (info: Cond.RegionInfo): BOOLEAN;
  (* If `info' belongs to a boolean guard, then check whether its predicate
     is known to be true or false.  In the former case add it to `trueList'
     and return TRUE, otherwise return FALSE.  *)
    VAR
      opcode, guardIndex: INTEGER;
      value: D.Usable;
      path: D.Region;
      
    PROCEDURE SinglePath (merge: D.Merge): D.Region;
      VAR
        r0, r1: D.Region;
      BEGIN
        r0 := merge. opndList. arg(D.Region);
        r1 := merge. opndList. nextOpnd. arg(D.Region);
        IF False (r0. info(Cond.RegionInfo). guard) THEN
          RETURN r1
        ELSIF False (r1. info(Cond.RegionInfo). guard) THEN
          RETURN r0
        ELSE
          RETURN NIL
        END
      END SinglePath;
    
    BEGIN
      opcode := info. region. opcode;
      IF (opcode = Opc.guardTrue) OR (opcode = Opc.guardFalse) THEN
        value := info. guard. value;
        IF (value = Sym.constTrue) THEN
          IF info. guard. negate THEN
            RETURN FALSE
          END
        ELSE
          guardIndex := ABS (SHORT (value. marker));
          IF (guardIndex <= notInspected) THEN
            AddToTrue (info. guard)
          ELSE
            IF (trueList[guardIndex]. negate # info. guard. negate) THEN
              RETURN FALSE
            END
          END
        END
      ELSIF (opcode = Opc.mergeCond) OR (opcode = Opc.mergeIf) THEN
        (* if one of the merge region is unreachable, add the other one to
           `trueList' *)
        path := SinglePath (info. region(D.Merge));
        IF (path # NIL) THEN
          RETURN AddGuardToTrue (path. info(Cond.RegionInfo))
        END
      END;
      RETURN TRUE
    END AddGuardToTrue;
  
  PROCEDURE AddGatesToTrue (gateOpnd: D.Opnd): BOOLEAN;
  (* Determines the merge to which `gateOpnd' belongs and adds all gates which
     are known to hold the value TRUE in the argument corresponding to 
     `gateOpnd' to the stack `trueList'.  *)
    VAR
      gate: D.Gate;
      merge: D.Merge;
      cond: Cond.Condition;
      use: D.Opnd;
      arg: D.Usable;
      gateIndex, argIndex, opn: INTEGER;
    BEGIN
      merge := gateOpnd. instr(D.Gate). opndList. arg(D.Merge);
      opn := gateOpnd. OperandIndex();
      use := merge. useList;
      WHILE (use # NIL) DO
        IF (use. instr IS D.Gate) THEN
          gate := use. instr(D.Gate);
          gateIndex := ABS (SHORT (gate. marker));
          IF (gateIndex > notInspected) THEN
            arg := gate. NthArgument (opn);
            IF (arg = Sym.constTrue) & trueList[gateIndex]. negate OR
               (arg = Sym.constFalse) & ~trueList[gateIndex]. negate THEN
              RETURN FALSE
            ELSIF (arg IS D.Result) THEN
              argIndex := ABS (SHORT (arg(D.Result). marker));
              IF (argIndex > notInspected) THEN
                IF (trueList[gateIndex].negate#trueList[argIndex].negate) THEN
                  RETURN FALSE
                END
              ELSE
                cond. value := arg;
                cond. negate := trueList[gateIndex]. negate;
                AddToTrue (cond)
              END
            END
          END
        END;
        use := use. nextUse
      END;
      RETURN TRUE
    END AddGatesToTrue;
  
  PROCEDURE PopTrue (oldCount: INTEGER);
    VAR
      i: INTEGER;
      res: D.Result;
    BEGIN
      FOR i := oldCount TO topOfStack-1 DO
        IF (trueList[i]. value IS D.Result) THEN
          res := trueList[i]. value(D.Result);
          IF (res. marker < 0) THEN
            res. marker := inspected
          ELSE
            res. marker := notInspected
          END
        END
      END;
      topOfStack := oldCount
    END PopTrue;
  
  
  PROCEDURE Test (i: INTEGER; opnd: D.Opnd): BOOLEAN;
  (* pre: `i' points past the last element of `infoList'. *)
    VAR
      info: Cond.RegionInfo;
      gateOpnd: D.Opnd;
      gate: D.Gate;
      skipLast, noContradiction: BOOLEAN;
      j, oldCount: INTEGER;
      newList: InfoList;
    BEGIN
      IF (opnd. arg = var) THEN
        RETURN TRUE
      ELSIF (opnd. arg(D.Result). instr. opcode # Opc.gate) THEN
        RETURN FALSE
      ELSE  (* the value of `opnd' is a gate *)
        gate := opnd. arg(D.Result). instr(D.Gate);
        IF (gate. var # var) THEN
          RETURN FALSE
        ELSE
          IF (i = LEN (infoList^)) THEN
            NEW (newList, i+128);
            FOR j := 0 TO i-1 DO
              newList[j] := infoList[j]
            END;
            infoList := newList
          END;
          
          skipLast := (gate. opndList. arg(D.Merge). opcode = Opc.mergeLoop);
          IF skipLast  THEN
            RETURN FALSE 
          END;
          
          oldCount := topOfStack;
          gateOpnd := gate. opndList. nextOpnd;
          WHILE (gateOpnd # NIL) DO
            info := Cond.OperandInfo (gateOpnd);
            noContradiction := TRUE;
            j := 0;
            WHILE noContradiction & (j < i) DO
              IF Cond.Contradicting (infoList[j], info) THEN
                noContradiction := FALSE
              END;
              INC (j)
            END;
            
            IF noContradiction THEN
              noContradiction := AddGatesToTrue (gateOpnd);
              IF noContradiction THEN
                j := topOfStack;
                noContradiction := AddGuardToTrue (Cond.OperandInfo (gateOpnd));
                IF noContradiction THEN
                  infoList[i] := info;
                  IF Test (i+1, gateOpnd) THEN
                    PopTrue (oldCount);
                    RETURN TRUE
                  ELSE
                    PopTrue (j)
                  END
                END
              END
            END;
            
            gateOpnd := gateOpnd. nextOpnd;
            IF skipLast THEN
              gateOpnd := NIL
            END;
            PopTrue (oldCount)
          END;
          RETURN FALSE
        END
      END
    END Test;
  
  BEGIN
    (* initialize `infoList'; it will hold the regions that are part of the 
       current path *)
    old := topOfStack;
    infoList[0] := Cond.OperandInfo (opnd);
    dummy := AddGuardToTrue (infoList[0]);
    dummy := Test (1, opnd);
    PopTrue (old);
    RETURN dummy
  END Reachable;
  
PROCEDURE InspectUses (var: D.Object; u: D.Usable; status: SHORTINT;
                       oldGates: D.Gate);
(* Inspect all uses of `u', marking potential undefined reads with warnings. 
   pre: `var. mode = D.objVar' *) 
  VAR
    use: D.Opnd;
    instr: D.Instruction;
    warn: INTEGER;
    param: D.Object;
    pos: LONGINT;
    
  PROCEDURE PushUse (use: D.Opnd);
    VAR
      new: UseStack;
      i: LONGINT;
    BEGIN
      IF (useStackSize = LEN (useStack^)) THEN
        NEW (new, LEN (useStack^)*2);
        FOR i := 0 TO LEN (useStack^)-1 DO
          new[i] := useStack[i];
          useStack[i] := NIL
        END
      END;
      useStack[useStackSize] := use;
      INC (useStackSize)
    END PushUse;
  
  PROCEDURE PopUse;
    BEGIN
      DEC (useStackSize);
      useStack[useStackSize] := NIL
    END PopUse;
  
  PROCEDURE IgnoredOperand (opnd: D.Opnd): BOOLEAN;
    BEGIN
      RETURN ~opnd. ValueOperand() OR opnd. PassThroughOperand()
    END IgnoredOperand;
  
  PROCEDURE NotCollectingOperand (opnd: D.Opnd): BOOLEAN;
  (* Returns TRUE iff `opnd' is part of the operand list to force a local 
     variable into $mem.  This is simply a test whether there is a $mem 
     argument in the operand list before `opnd'.  *)
    VAR
      memOpnd: D.Opnd;
    BEGIN
      memOpnd := opnd. instr. GetOperand (Sym.mem, D.symLocObject);
      WHILE (memOpnd # NIL) & (memOpnd # opnd) DO
        memOpnd := memOpnd. nextOpnd
      END;
      RETURN (memOpnd = NIL)
    END NotCollectingOperand;

  PROCEDURE UnknownProcedure (call: D.Instruction): BOOLEAN;
    VAR
      arg: D.Usable;
    BEGIN
      arg := call. NthArgument (2);
      RETURN (arg = D.constUndef) OR
             (arg(D.Object). mode = D.objTBProc)
    END UnknownProcedure;
  
  PROCEDURE Contradicting (use: D.Opnd): BOOLEAN;
  (* Return TRUE if any of the gate uses on the path to `use' contradict with
     the evaluation of the instruction of `use'.  *)
    VAR
      i: LONGINT;
      ri1: Cond.RegionInfo;
    BEGIN
      ri1 := Cond.OperandInfo (use);
      i := useStackSize;
      WHILE (i > 0) DO
        DEC (i);
        IF Cond.Contradicting (ri1, Cond.OperandInfo (useStack[i])) THEN
          RETURN TRUE
        END
      END;
      RETURN FALSE
    END Contradicting;
  
  PROCEDURE AbstractProc (var: D.Object): BOOLEAN;
  (* TRUE iff procedure declaring `var' is abstract *)
    BEGIN
      RETURN (D.objAbstractTBProc IN var. localTo(D.Object). flags)
    END AbstractProc;
  
  BEGIN
    use := u. useList;
    WHILE (use # NIL) DO
      IF ~IgnoredOperand (use) & ~Contradicting (use) THEN
        instr := use. instr;
        warn := 0;
        IF (instr. opcode = Opc.exit) & (var. name^ # "$result") THEN
          (* ignore *)
          
        ELSIF (instr. opcode = Opc.gate) THEN
          IF (instr. marker > 0) THEN
            instr. marker := -instr. marker;
            IF (instr. opndList. arg(D.Merge). opcode # Opc.mergeLoop) OR
               (instr. opndList. nextOpnd # use) THEN
              PushUse (use);
              InspectUses (var, instr, maybeUndefined, instr(D.Gate));
              PopUse
            END
          END
          
        ELSIF (instr. opcode = Opc.call) THEN
          (* operand belongs to a procedure call *)
          param := use. GetFormalParam();
          IF UnknownProcedure (instr) THEN
            (* the call activates a procedure variable or a type-bound 
               procedure; there is no information on the use of the 
               parameter *)
          ELSIF (param = NIL) THEN
            warn := 414     (* procedure may access uninitialized variable  *)
          ELSIF (param. mode = D.objVar) THEN
            IF (status = undefined) THEN
              warn := 404   (* variable is used uninitialized *)
            ELSE
              warn := 405   (* variable may be used uninitialized *)
            END
          ELSIF (param. mode = D.objVarPar) &
                (D.objReadBeforeWrite IN param. flags) THEN
            warn := 415     (* variable parameter may be used uninitialized *)
          END
          
        ELSE
          IF (status = undefined) THEN
            warn := 404               (* variable is used uninitialized *)
          ELSE
            warn := 405               (* variable may be used uninitialized *)
          END
        END;

        IF (warn > 0) & Reachable (var, use) & (warn # 414) &
           NotCollectingOperand (use) & ~Contradicting (use) THEN
          (* emit warning *)
          pos := use. pos;
          IF (use. pos < 0) THEN
            pos := instr. pos
          END;
          IF (var. name^ = "$result") THEN  (* RETURN (maybe) missing *)
            INC (warn, 2);
            pos := S.currSymPos;
            IF AbstractProc (var) THEN
              warn := 0
            END
          END;
          
          IF (warn = 414) THEN
            E.ErrIns (pos, -warn, var. name^)
          ELSIF (warn > 0) THEN
            E.Err (pos, -warn)
          END
        END
      END;
      use := use. nextUse
    END
  END InspectUses;

PROCEDURE ReadsEmptyStore (var: D.Object): BOOLEAN;
(* Returns TRUE if an access instruction to `var' reads or may read from 
   the initial store value, i.e. the result of the create-store instruction.
   pre: `var. mode = D.objVarPar'  *)
  VAR
    use: D.Opnd;
    greg: D.GlobalRegion;
    formalParam: D.Object;
  BEGIN
    use := var. useList;
    WHILE (use # NIL) DO
      IF (use. instr. opcode = Opc.accessVarParam) &
         (use. instr. useList # NIL) &
         ((use. instr. useList. nextUse # NIL) OR 
          (use. instr. useList. instr. opcode # Opc.exit)) & 
         Attr.TracesToEmptyStore (var, use. instr. NthArgument (2)) THEN
        (* ignore unused accesses (they are dead code) and accesses in
           nested procedures *)
        greg := use. instr. region. Greg();                  
        IF (greg. bodyOf = var. localTo) THEN
          (* ignore if value is passed to parameter that isn't read before
             write *)
          IF (use. instr. useList. instr. opcode = Opc.call) THEN
            formalParam := use. instr. useList. GetFormalParam();
            IF (formalParam = NIL) OR
               (D.objReadBeforeWrite IN formalParam. flags) THEN
              RETURN TRUE
            END
          ELSE 
            RETURN TRUE
          END
        END
      END;
      use := use. nextUse
    END;
    RETURN FALSE
  END ReadsEmptyStore;

PROCEDURE CheckVars* (greg: D.GlobalRegion; VAR exitInfo: Attr.ExitInfo);
(* Checks that values of local variables aren't used prior to any assignment 
   and that a function procedure is left with a RETURN statement.*)
  VAR
    exit: D.Instruction;
    exitRegion: D.Region;
    i: INTEGER;
    
  PROCEDURE InspectLocalVars (obj: D.Object);
  (* If `obj' is a variable of unstructure type, then inspect all uses of `obj'
     for reading access.  If `obj' is a variable parameter that is read before
     written to, then mark the parameter object with `D.objReadBeforeWrite'. *)
    VAR
      param: D.Object;
    BEGIN
      IF (obj # NIL) THEN
        InspectLocalVars (obj. leftObj);
        IF (obj. type # NIL) & 
           ~Sym.TypeInGroup (obj. type, D.grpStructured) THEN
          IF (obj. mode = D.objVar) & ~(D.objIsParameter IN obj. flags) THEN
            InspectUses (obj, obj, undefined, NIL)
          ELSIF (obj. mode = D.objVarPar) THEN
            (* remember that there are two copies of formal parameter objects:
               one in the symbol table (`obj') and one that is used for
               everything else (`param') *)
            param := obj. data(D.Object);
            IF ReadsEmptyStore (param) THEN
              INCL (param. flags, D.objReadBeforeWrite)
            END
          END
        END;
        InspectLocalVars (obj. rightObj)
      END
    END InspectLocalVars;
  
  PROCEDURE MarkNotInspected (instr: D.Instruction);
  (* Marks results of all instructions of `instr' and, if it's a region, of all
     instructions nested in it, as notInspected.  *)
    VAR
      result: D.Result;
    BEGIN
      result := instr;
      WHILE (result # NIL) DO
        result. marker := notInspected;
        result := result. nextResult
      END;
      IF (instr IS D.Region) THEN       (* traverse instructions in region *)
        instr := instr(D.Region). instrList;
        WHILE (instr # NIL) DO
          MarkNotInspected (instr);
          instr := instr. nextInstr
        END
      END
    END MarkNotInspected;
  
  PROCEDURE InitTrueList (r: D.Region);
    VAR
      i: D.Instruction;
      c: Cond.Condition;
    BEGIN
      i := r. instrList;
      WHILE (i # NIL) DO
        IF (i IS D.Region) THEN
          InitTrueList (i(D.Region))
        ELSIF (i. opcode = Opc.copy) & (i. type # NIL) &
              (i. type. form = D.strBoolean) &
              (i. opndList. arg IS D.Const) THEN
          c. value := i;
          c. negate := (i. opndList. arg # Sym.constTrue);
          AddToTrue (c)
        END;
        i := i. nextInstr
      END
    END InitTrueList;
  
  BEGIN
    Cond.Init (greg);  (* construct info of contradicting regions *)
    MarkNotInspected (greg);
    topOfStack := 2;  (* start at 2 to avoid conflicts with other markers *)
    InitTrueList (greg);
    InspectLocalVars (greg. bodyOf. localDecl);
    IF (exitInfo. result # NIL) THEN
      exit := greg. ExitInstr();
      exitRegion := exit. region;
      exitRegion. region. MoveInstruction (exit);
      InspectUses (exitInfo. result, exitInfo. result, undefined, NIL);
      exitRegion. MoveInstruction (exit)
    END;
    
    (* get rid of unused references to heap *)
    FOR i := 0 TO SHORT (LEN (infoList^))-1 DO
      infoList[i] := NIL
    END;
    FOR i := 0 TO SHORT (LEN (trueList^))-1 DO
      trueList[i]. value := NIL
    END
  END CheckVars;

BEGIN
  NEW (infoList, 128);
  NEW (trueList, 128);
  NEW (useStack, 32);
  useStackSize := 0
END UndefVar.
