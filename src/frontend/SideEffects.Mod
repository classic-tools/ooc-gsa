(* 	$Id: SideEffects.Mod,v 1.19 1999/06/27 19:38:31 acken Exp $	 *)
MODULE SideEffects;
(*  Corrects side-effect information of forward calls.
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

IMPORT
  D := Data, Opc := Opcode, Sym := SymbolTable, Attr := Attributes;


(*
This module provides procedures to determine and install exact side-effect
information for procedure calls whose side-effects were conservatively
approximated by $mem.

Such an approximation is inserted by the front-end for every call of a 
procedure that is defined later in the text.  There are three different ways
to do such a forward call:
 a) call an explicitly forward declared procedure that hasn't been defined yet
 b) from within a nested procedure call an enclosing procedure
 c) recursively activate a procedure.
For all of these calls the front-end has to assumed the worst, namely that the
callee reads and changes arbitrary memory locations.  

As soon as all involved procedures are defined, the conservative approximation
can be replaced by an account of the procedure's excact side-effect (reading
and writing).  If the back-end only considers the code of a single procedure
at a time, and discards its code as soon as it's translated, then only case c)
can be improved.

To use this module, do
  1) call Init
  2) call AddProc for every procedure that should be considered in the 
     calculation 
  3) call Adjust
Note that only calls from within procedures registered in step 2) to equally
registered procedures are changed.

Note: This module has to be called before any alias analysis.  The reason for
this is that it has to reconstruct designators from the GSA code, which isn't
possible (yet) if e.g. the value of `r.a' is replaced by a constant.
*)

TYPE
  ProcInfo = POINTER TO ProcInfoDesc;
  InfoList = POINTER TO InfoListDesc;
  ProcInfoDesc = RECORD
    (D.InfoDesc)
    next, nextWorklist: ProcInfo;
    greg: D.GlobalRegion;
    enter, exit: D.Instruction;
    flags: SET;
    callerList: InfoList;

    enterPtr: D.Result;
    exitPtr: D.Opnd;
    oldInfo: D.Info
  END;
  InfoListDesc = RECORD
    next: InfoList;
    info: ProcInfo
  END;

  CallInfo = POINTER TO CallInfoDesc;
  CallInfoDesc = RECORD
    (D.InfoDesc)
    caller: D.Object;                    (* calling procedure *)
    callee: D.Object;                    (* called procedure *)
    memIn: D.Opnd;                       (* $mem operand of call *)
    memOut: D.Result;                    (* $mem result of call *)
    storeIn: D.Opnd;                     (* $store operand of call *)
    storeOut: D.Result;                  (* $store result of call *)
    flags: SET;
    
    (* while doing our work we don't want to have any operands around that were
       inserted to collect a variable into $mem, likewise for reclaiming 
       results; for the duration of the algorithm these operand and result 
       lists are moved into these variables: *)
    savedResults: D.Result;
    savedOpnds: D.Opnd
  END;


CONST  (* symbolic values for field `ProcInfo.flags' *)
  markedReadMem = 0;
  (* the initial enter instruction provides a value for $mem, i.e. the
     procedure reads arbitrary memory contents *)
  markedWriteMem = 1;
  (* the initial exit instruction has an operand called $mem, i.e. the
     procedure writes into unknown memory regions *)
  doesReadMem = 2;
  (* one of the greg's instructions does read from $mem *)
  doesWriteMem = 3;
  (* one of the greg's instructions does write to $mem *)
  inWorklist = 4;
  (* greg is part of the current worklist *)
  markedNotDead = 5;
  (* the initial enter instruction is marked with `instrNotDead' *)
  isNotDead = 6;
  (* execution of the procedure may raise an exception *)

CONST  (* symbolic values for field `CallInfo.flags' *)
  readsFromStore = 0;
  (* the procedure call accesses a variable that is in $store as seen from the
     calling procedure *)
  writesToStore = 1;
  (* the procedure call modifies a variable that is in $store as seen from the
     calling procedure *)
     
VAR
  gregList: ProcInfo;


PROCEDURE Init*;
(* Clears list of analysed global regions.  *)
  BEGIN
    gregList := NIL
  END Init;

PROCEDURE AddProc* (greg: D.GlobalRegion);
(* Adds `greg' to the list of global regions that should be considered when
   analysing the side-effect information.  This also means that the side-
   effects of `greg', as described in its enter and exit instruction, will be
   adjusted whenever possible.  In the ideal case a reference from/to $mem
   will be replaced by the exact side-effects.  
   If `greg' is NIL, nothing will be done.  *)
  VAR
    i: ProcInfo;
    res, memResult: D.Result;
    memOpnd: D.Opnd;
  BEGIN
    IF (greg # NIL) THEN
      NEW (i);
      i. next := gregList;
      i. nextWorklist := NIL;
      i. greg := greg;
      i. enter := greg. EnterInstr();
      i. exit := greg. ExitInstr();
      i. flags := {};
      
      (* check if enter has a $mem result; if this is the case move the end
         of the result list (after the $mem) to a local data structure *)
      memResult := i. enter. GetResult (Sym.mem, D.symLocObject);
      IF (memResult # NIL) THEN
        INCL (i. flags, markedReadMem)
      END;
      
      (* check if exit has a $mem operand; if this is the case move the end
         of the operand list (after the $mem) to a local data structure *)
      memOpnd := i. exit. GetOperand (Sym.mem, D.symLocObject);
      IF (memOpnd # NIL) THEN
        INCL (i. flags, markedWriteMem)
      END;
      
      IF (D.instrNotDead IN i. enter. flags) THEN
        INCL (i. flags, markedNotDead);
        INCL (i. flags, isNotDead)
      END;
      i. callerList := NIL;
      res := i. enter. nextResult;
      WHILE (res # NIL) &  (* skip formal parameters *)
            (res. location # NIL) &
            (res. location IS D.SymLocation) &
            (res. location(D.SymLocation). var IS D.Object) &
            (res. location(D.SymLocation). var(D.Object). localTo = greg. bodyOf) DO
        res := res. nextResult
      END;
      i. enterPtr := res;
  
      IF (i. exit # NIL) THEN
        i. exitPtr := i. exit. opndList
      END;
  
      i. oldInfo := i. greg. info;
      i. greg. info := i;
      gregList := i
    END
  END AddProc;

PROCEDURE Append (VAR list: InfoList; info: ProcInfo);
  BEGIN
    IF (list = NIL) THEN
      NEW (list);
      list. next := NIL;
      list. info := info
    ELSIF (list. info # info) THEN
      Append (list. next, info)
    END
  END Append;


PROCEDURE Adjust*;
  VAR
    i: ProcInfo;
    use, opnd0: D.Opnd;
    res0: D.Result;

  PROCEDURE RegisteredCall (instr: D.Instruction): BOOLEAN;
  (* TRUE iff `instr' is a call activating a registered procedure.  *)
    VAR
      callee: D.Usable;
    BEGIN
      IF (instr. opcode # Opc.call) THEN
        RETURN FALSE
      ELSIF ~(instr. opndList. arg IS D.Instruction) OR
            (instr. opndList. arg(D.Instruction). opcode # Opc.adr) THEN
        (* either calling a procedure variable or a type-bound procedure 
           with dynamic binding *)
        RETURN FALSE
      ELSE
        callee := instr. NthArgument (2);
        RETURN (callee IS D.Object) &
               (callee(D.Object). greg # NIL) &
               (callee(D.Object). greg. info # NIL) &
               (callee(D.Object). greg. info IS ProcInfo)
      END
    END RegisteredCall;

  PROCEDURE ExamineInstructions (i: ProcInfo; r: D.Region);
  (* For every call to an registered procedure add `i' to the callee's list of
     callers.  If any instruction in `r' reads from or writes to $mem, then set
     in `i. flags' the flags `doesReadMem', or `doesWriteMem', respectively. *)
    VAR
      instr: D.Instruction;
      opc: INTEGER;
      callee: D.Usable;
      
    PROCEDURE GetCallInfo (call: D.Instruction): CallInfo;
      VAR
        cinfo: CallInfo;
        greg: D.GlobalRegion;
      BEGIN
        NEW (cinfo);
        greg := call. Greg();
        cinfo. caller := greg. bodyOf;
        cinfo. callee := call. opndList. nextOpnd. nextOpnd. arg(D.Object);
        cinfo. memIn := call. GetOperand (Sym.mem, D.symLocObject);
        cinfo. storeIn := call. GetOperand (Sym.store, D.symLocObject);
        cinfo. memOut := call. GetResult (Sym.mem, D.symLocObject);
        cinfo. storeOut := call. GetResult (Sym.store, D.symLocObject);
        IF (cinfo. memOut # NIL) THEN
          D.TransferResultList (cinfo. memOut, cinfo. savedResults, FALSE)
        ELSE
          cinfo. savedResults := NIL
        END;
        IF (cinfo. memIn # NIL) THEN
          D.TransferOperandList (cinfo. memIn, cinfo. savedOpnds, FALSE)
        ELSE
          cinfo. savedOpnds := NIL
        END;
        RETURN cinfo
      END GetCallInfo;

    BEGIN
      instr := r. instrList;
      WHILE (instr # NIL) DO
        WITH instr: D.Region DO
          ExamineInstructions (i, instr)
        ELSE
          opc := instr. opcode;

          IF RegisteredCall (instr) THEN
            callee := instr. NthArgument (2);
            Append (callee(D.Object). greg. info(ProcInfo). callerList, i);
            instr. info := GetCallInfo (instr)

          ELSIF (opc = Opc.call) OR (opc = Opc.bit) OR (opc = Opc.move) OR
                (opc = Opc.updateMem) OR (opc = Opc.accessMem) THEN
            (* check if the instruction accesses $mem, set flags accordingly;
               all other instructions do not touch $mem; in particular skip
               enter and exit *)
            IF (instr. GetResult (Sym.mem, D.symLocObject) # NIL) THEN
              INCL (i. flags, doesWriteMem)
            END;
            IF (instr. GetOperand (Sym.mem, D.symLocObject) # NIL) THEN
              INCL (i. flags, doesReadMem)
            END
          END
        END;
        instr := instr. nextInstr
      END
    END ExamineInstructions;

  PROCEDURE PropagateSideEffects;
    VAR
      worklist, i: ProcInfo;
      caller: InfoList;
      res, newRes, res0: D.Result;
      opnd, newOpnd, lopnd: D.Opnd;
      var, lvar: D.Addressable;
      lattrib: INTEGER;
      varParam: BOOLEAN;
      enter: D.Instruction;

    PROCEDURE AddToWorklist (caller: ProcInfo;
                             enterPtr: D.Result; exitPtr: D.Opnd);
      VAR
        inWorklist: BOOLEAN;
      BEGIN
        inWorklist := (caller. enterPtr # NIL) OR (caller. exitPtr # NIL);
        IF (enterPtr # NIL) THEN
          caller. enterPtr := enterPtr
        END;
        IF (exitPtr # NIL) THEN
          caller. exitPtr := exitPtr
        END;
        IF ~inWorklist THEN
          caller. nextWorklist := worklist. nextWorklist;
          worklist. nextWorklist := caller
        END
      END AddToWorklist;

    PROCEDURE AddSideEffect (caller: ProcInfo;
                             var: D.Addressable; attrib: INTEGER);
      VAR
        exit: D.Instruction;
      BEGIN
        exit := caller. greg. ExitInstr();
        IF (exit. GetOperand (var, attrib) = NIL) &
           ((var IS D.Struct) OR
            (var(D.Object). localTo # caller. greg. bodyOf)) THEN
          (* the caller doesn't know about this particular side-effect and the
             variable isn't local to the caller: add it to the exit
             instruction *)
          exit. Operand (D.constUndef);
          newOpnd := exit. LastOperand();
          newOpnd. location := D.CreateSymLocation (var, attrib);

          (* if the caller isn't in the worklist, add it (again) *)
          IF (caller. exitPtr = NIL) THEN
            AddToWorklist (caller, NIL, newOpnd)
          END
        END
      END AddSideEffect;

    PROCEDURE GetDesignatorBase (u: D.Usable): D.Addressable;
      VAR
        instr: D.Instruction;
      BEGIN
        IF (u IS D.Object) THEN  (* local uninitialized variable *)
          RETURN NIL
        ELSE
          instr := u(D.Result). instr;
          CASE instr. opcode OF
          | Opc.accessField, Opc.accessElement, Opc.typeGuard:
            RETURN GetDesignatorBase (instr. opndList. arg)
          | Opc.accessHeap, Opc.accessNonlocal, Opc.accessVarParam:
            RETURN instr. opndList. arg(D.Addressable)
          ELSE
            RETURN NIL
          END
        END
      END GetDesignatorBase;

    BEGIN
      (* create worklist *)
      worklist := NIL;
      i := gregList;
      WHILE (i # NIL) DO
        IF (i. enterPtr # NIL) OR (i. exitPtr # NIL) THEN
          i. nextWorklist := worklist;
          worklist := i
        END;
        i := i. next
      END;

      (* until worklist is empty: propagate side-effect (reading or writing) of
         the first greg in the list to all its callers *)
      WHILE (worklist # NIL) DO
        res := worklist. enterPtr;

        WHILE (res # NIL) DO
          IF (res. location(D.SymLocation). var # Sym.mem) THEN
            lvar := res. location(D.SymLocation). var;
            lattrib := res. location(D.SymLocation). attrib;
            caller := worklist. callerList;
            WHILE (caller # NIL) DO
              enter := caller. info. greg. EnterInstr();
              IF (enter. GetResult (lvar, lattrib) = NIL) &
                 ((lvar IS D.Struct) OR
                  (lvar(D.Object). localTo # caller. info. greg. bodyOf)) THEN
                (* the caller doesn't know about this particular side-effect
                   and the variable isn't local to the caller: add it to the
                   enter instruction *)
                newRes := enter. AppendResult (res. location, res. type);

                (* the the caller isn't in the worklist, add it (again) *)
                IF (caller. info. enterPtr = NIL) THEN
                  AddToWorklist (caller. info, newRes, NIL)
                END
              END;
              caller := caller. next
            END
          END;

          res := res. nextResult
        END;
        worklist. enterPtr := NIL;

        opnd := worklist. exitPtr;
        WHILE (opnd # NIL) DO
          var := opnd. location(D.SymLocation). var;
          IF (var # Sym.mem) &
             ((var IS D.Struct) OR
              (var(D.Object). name^ # "$result")) THEN
            (* the operand doesn't set a new $mem value and is either a heap
               object or a nonlocal variable; ignore the function result *)
            varParam := (var IS D.Object) &
                        (var(D.Object). localTo = worklist. greg. bodyOf);
            lattrib := opnd. location(D.SymLocation). attrib;
            caller := worklist. callerList;
            WHILE (caller # NIL) DO
              IF varParam THEN
                (* update of variable parameter: for every call of `i' from
                   `caller' examine base of updated designator and register it
                   as side-effect (if necessary) *)
                use := worklist. greg. bodyOf. useList;
                WHILE (use # NIL) DO
                  IF (use. instr. opcode = Opc.call) &
                     (use. instr. NthOperand (2) = use) &
                     (use. Greg() = caller. info. greg) THEN
                    res0 := worklist. enter. GetResult (var, D.symLocObject);
                    lopnd := use. instr. NthOperand (2+res0. ResultIndex());
                    IF (lopnd. arg IS D.Const) THEN
                      (* can't reconstruct designator from a constant: take
                         operand of following address instruction *)
                      ASSERT ((lopnd. nextOpnd. arg IS D.Instruction) &
                              (lopnd. nextOpnd. arg(D.Instruction). opcode = Opc.adr));
                      lvar := lopnd. nextOpnd. arg(D.Instruction). opndList. arg(D.Addressable)
                    ELSE
                      lvar := GetDesignatorBase (lopnd. arg)
                    END;
                    IF (lvar # NIL) THEN
                      AddSideEffect (caller. info, lvar, D.symLocObject)
                    END
                  END;
                  use := use. nextUse
                END
              ELSE
                AddSideEffect (caller. info, var, lattrib)
              END;
              caller := caller. next
            END
          END;

          opnd := opnd. nextOpnd
        END;
        worklist. exitPtr := NIL;

        worklist := worklist. nextWorklist
      END
    END PropagateSideEffects;

  PROCEDURE PropagateMem;
    VAR
      worklist, i: ProcInfo;
      c: InfoList;
      add: BOOLEAN;
    BEGIN
      (* create worklist *)
      worklist := NIL;
      i := gregList;
      WHILE (i # NIL) DO
        IF (i. flags * {doesReadMem, doesWriteMem, isNotDead} # {}) THEN
          i. nextWorklist := worklist;
          worklist := i;
          INCL (i. flags, inWorklist)
        END;
        i := i. next
      END;

      (* propagate `doesReadMem', `doesWriteMem', and `isNotDead' flags to 
         caller *)
      WHILE (worklist # NIL) DO
        i := worklist;
        worklist := worklist. nextWorklist;
        EXCL (i. flags, inWorklist);

        c := i. callerList;
        WHILE (c # NIL) DO
          add := FALSE;

          IF (doesReadMem IN i. flags) & ~(doesReadMem IN c. info. flags) THEN
            INCL (c. info. flags, doesReadMem);
            add := TRUE
          END;
          IF (doesWriteMem IN i. flags) &~(doesWriteMem IN c. info. flags) THEN
            INCL (c. info. flags, doesWriteMem);
            add := TRUE
          END;
          IF (isNotDead IN i. flags) & ~(isNotDead IN c. info. flags) THEN
            INCL (c. info. flags, isNotDead);
            add := TRUE
          END;
          
          IF add & ~(inWorklist IN c. info. flags) THEN
            c. info. nextWorklist := worklist;
            worklist := c. info;
            INCL (c. info. flags, inWorklist)
          END;

          c := c. next
        END
      END
    END PropagateMem;

  PROCEDURE AdjustGSA (i: ProcInfo);
    VAR
      opnd, use, opnd0: D.Opnd;
      greg: D.GlobalRegion;
      res: D.Result;
      store: D.Result;
      
    PROCEDURE SameLocation (a, b: D.Location): BOOLEAN;
      BEGIN
        RETURN (a # NIL) & (b # NIL) &
               (a IS D.SymLocation) & (b IS D.SymLocation) &
               (a(D.SymLocation). var = b(D.SymLocation). var) &
               (a(D.SymLocation). attrib = b(D.SymLocation). attrib)
      END SameLocation;

    PROCEDURE Address (region: D.Region; var: D.Addressable; 
                       pos: LONGINT): D.Result;
      VAR
        greg: D.GlobalRegion;
      BEGIN
        greg := region. Greg();
        IF (var IS D.Object) & 
           ((var(D.Object). mode = D.objVarPar) OR
            ((var(D.Object). mode = D.objVar) &
             (var(D.Object). localTo # greg. bodyOf))) THEN
          RETURN Attr.FindAddEnterResult (region, var, D.symLocAddress, 
                                          D.struct[D.strAddress])
        ELSE
          RETURN region. CreateAdrInstr (var, pos);
        END
      END Address;
    
    PROCEDURE AdjustResults (call: D.Instruction; cinfo: CallInfo);
      VAR
        res, res0: D.Result;
        opnd, adrIn, opnd0: D.Opnd;
        var: D.Addressable;
        inputVar: D.Object;
        loc: D.SymLocation;
        enter: D.Instruction;

      PROCEDURE UpdateVar (var: D.Object; value: D.Usable);
      (* Update output value of call instruction for variable `var' to
         `value'.  *)
        VAR
          instr: D.Instruction;
          res: D.Result;
          opcode: INTEGER;
        BEGIN
          IF (var. localTo = cinfo. caller) & (var. mode = D.objVar) THEN
            (* writing to local variable of the caller *)
            IF (cinfo. memOut # NIL) THEN
              (* search value of local variable that was previously reclaimed
                 from $mem; replace it with the new value `value' *)
              res := cinfo. savedResults;
              WHILE (res. location(D.SymLocation). var # var) DO
                res := res. nextResult
              END;
              res. ReplaceUses (value)
            END
            
          ELSE (* writing to nonlocal variable or variable parameter *)
            IF (var. localTo = cinfo. caller) THEN
              opcode := Opc.updateVarParam
            ELSE
              opcode := Opc.updateNonlocal
            END;

            instr := call. region. CreateInstruction (opcode, var. type, call. pos);
            cinfo. storeOut. ReplaceUses (instr);
            instr. Operand (var);
            instr. Operand (Address (call. region, var, call. pos));
            instr. Operand (cinfo. storeOut);
            instr. Operand (value);
            cinfo. storeOut := instr
          END
        END UpdateVar;

      PROCEDURE LocalVarAdr (u: D.Usable): D.Object;
      (* If `u' is an adr instruction that takes a local variable object of the
         caller as argument, then return this variable.  Otherwise return
         NIL.  *)
        VAR
          arg: D.Usable;
        BEGIN
          IF (u IS D.Instruction) & (u(D.Instruction). opcode = Opc.adr) THEN
            arg := u(D.Instruction). opndList. arg;
            IF (arg IS D.Object) & (arg(D.Object). mode = D.objVar) &
               (arg(D.Object). localTo(D.Object). greg =
                u. Greg()) THEN
              RETURN arg(D.Object)
            END
          END;
          RETURN NIL
        END LocalVarAdr;

      PROCEDURE UpdateDesignator (access: D.Instruction; value: D.Usable);
        VAR
          opcode: INTEGER;
          update: D.Instruction;
          opnd: D.Opnd;
        BEGIN
          IF (access. opcode = Opc.typeGuard) THEN
            UpdateDesignator (access. opndList. arg(D.Instruction), value)
          ELSE
            opcode := access. opcode+Opc.sizeClass;
            update := call. region. CreateInstruction (opcode, access. opndList. OpndType(), call. pos);
            opnd := access. opndList;
            WHILE (opnd # NIL) DO
              update. Operand (opnd. arg);  (* store operand is set later *)
              opnd := opnd. nextOpnd
            END;
            update. Operand (value);

            CASE opcode OF
            | Opc.updateField, Opc.updateElement:
              UpdateDesignator (update. opndList. arg(D.Instruction), update)
            | Opc.updateNonlocal, Opc.updateVarParam, Opc.updateHeap:
              cinfo. storeOut. ReplaceUses (update);
              opnd := update. NthOperand (2);
              opnd. ReplaceOperand (cinfo. storeOut);
              cinfo. storeOut := update
            END
          END
        END UpdateDesignator;

      PROCEDURE LocalVar (l: D.SymLocation; proc: D.Object): BOOLEAN;
        BEGIN
          IF (l. var IS D.Object) THEN
            RETURN (l. var(D.Object). localTo = proc)
          ELSE
            RETURN FALSE
          END
        END LocalVar;

      PROCEDURE GetSymLoc (var: D.Addressable; greg: D.GlobalRegion): D.SymLocation;
        BEGIN
          IF (var IS D.Object) &
             (var(D.Object). localTo(D.Object). greg = greg) THEN
            RETURN D.CreateSymLocation (var, D.symLocObject)
          ELSE
            RETURN NIL
          END;
        END GetSymLoc;

      PROCEDURE IsResult (opnd: D.Opnd): BOOLEAN;
        VAR
          l: D.SymLocation;
        BEGIN
          IF (opnd = NIL) THEN
            RETURN FALSE
          ELSE
            l := opnd. location(D.SymLocation);
            RETURN (l. var IS D.Object) &
                   (l. var(D.Object). name^ = "$result")
          END
        END IsResult;
      
      PROCEDURE IsFormalParam (callee: D.Object; loc: D.SymLocation): BOOLEAN;
        BEGIN
          RETURN (loc. var IS D.Object) &
                 (loc. var(D.Object). localTo = callee)
        END IsFormalParam;
      
      BEGIN
        IF (i. exit = NIL) THEN
          (* the called procedure has no exit instruction; this means it is 
             never left, e.g. due to an endless loop or a HALT; tell dead code
             elimination to leave this call alone *)
          INCL (call. flags, D.instrNotDead)
          
        ELSE
          (* compare results of `call' with operands of `i. exit';
             move pointer to exit operands to the first operand that doesn't 
             have a corresponding result; skip $result on the way *)
          res := call. nextResult;
          opnd := i. exit. opndList;
          IF IsResult (opnd) THEN opnd := opnd. nextOpnd END;

          WHILE (res # NIL) & (opnd # NIL) &
                ((res. location = NIL) OR
(*simplify?...*) LocalVar (res. location(D.SymLocation), cinfo. caller) OR
                 SameLocation (res. location, opnd. location)) DO
            IF ~IsFormalParam (cinfo. callee, opnd. location(D.SymLocation)) &
               Attr.PartOfStore (cinfo. caller, opnd. location) THEN
              INCL (cinfo. flags, writesToStore)
            END;
            res := res. nextResult;
            opnd := opnd. nextOpnd;
            IF IsResult (opnd) THEN opnd := opnd. nextOpnd END
          END;

          (* for every following operand `opnd' add a new result to the call
             instruction *)
          WHILE (opnd # NIL) DO
            IF ~IsFormalParam (cinfo. callee, opnd. location(D.SymLocation)) &
               Attr.PartOfStore (cinfo. caller, opnd. location) THEN
              INCL (cinfo. flags, writesToStore)
            END;
            
            var := opnd. location(D.SymLocation). var;
            WITH var: D.Object DO
              IF (var = Sym.mem) THEN
                IF (doesWriteMem IN i. flags) THEN
                  (* replace previous $mem result with one that corresponds to
                     the position of $mem in the callee's exit instruction *)
                  res := call. AppendResult (D.CreateSymLocation (
                                                Sym.mem, D.symLocObject), NIL);
                  cinfo. memOut. ReplaceUses (res);
                  cinfo. memOut. DeleteResult();
                  cinfo. memOut := res
                END

              ELSIF (var. name^ = "$result") THEN
                (* ignore the `official' result *)

              ELSIF (var. localTo = i. greg. bodyOf) THEN
                (* called procedure writes to variable parameter `var' *)
                enter := i. greg. EnterInstr();
                res0 := enter. GetResult (var, D.symLocAddress);
                adrIn := call. NthOperand (2+res0. ResultIndex());
                inputVar := LocalVarAdr (adrIn. arg);
                IF (inputVar # NIL) THEN
                  (* local variable is passed to variable parameter *)
                  opnd0 := call. GetOperand (inputVar, D.symLocObject);
                  UpdateVar (inputVar, call. AppendResult (D.CreateSymLocation (inputVar, D.symLocObject), opnd0. OpndType()))
                ELSE  (* complex designator is passed to var parameter *)
                  adrIn := call. GetOperand (var, D.symLocObject);
                  UpdateDesignator (adrIn. arg(D.Instruction),
                                         call. AppendResult (NIL, var. type))
                END

              ELSE
                (* writing to local variable or variable parameter of the
                   caller, or a nonlocal variable of the enclosing procedure
                   or the of module itself *)
                loc := GetSymLoc (var, call. Greg());
                UpdateVar (var, call. AppendResult (loc, var. type))
              END

            | var: D.Struct DO
              (* called procedure writes to heap object of type `var' *)
              res := call. AppendResult (opnd. location, NIL)
            END;
            opnd := opnd. nextOpnd
          END
        END;

        IF ~(doesWriteMem IN i. flags) THEN
          IF (cinfo. memOut # NIL) THEN
            (* called procedure doesn't write to $mem *)
            cinfo. memOut. ReplaceUses (cinfo. memIn. arg);
            cinfo. memOut. DeleteResult()
          END
        END
      END AdjustResults;

    PROCEDURE GetFinalStore (r: D.Region): D.Result;
    (* Returns the value of $store that is valid at the very end of the
       procedure.  It is taken from the operand of the delete-store
       instruction.  *)
      VAR
        i: D.Instruction;
      BEGIN
        i := r. instrList;
        store := NIL;
        WHILE (i # NIL) & (store = NIL) DO
          IF (i IS D.Region) THEN
            store := GetFinalStore (i(D.Region))
          ELSIF (i. opcode = Opc.deleteStore) THEN
            store := i. opndList. arg(D.Result)
          END;
          i := i. nextInstr
        END;
        RETURN store
      END GetFinalStore;

    PROCEDURE SetExitOpnd (exit: D.Instruction; opnd: D.Opnd; store: D.Result);
    (* Provides a new operand of the exit instruction with its correct value.
       `opnd' is a side-effect that has been added by `PropagateSideEffects' to
       the procedure; `store' is the value of the pseudo-variable $store at the
       end of the procedure.  *)
      VAR
        var: D.Addressable;
        instr: D.Instruction;
      BEGIN
        var := opnd. location(D.SymLocation). var;
        WITH var: D.Object DO
          (* procedure changed the value of the nonlocal variable `var' *)
          instr := exit. region. CreateInstruction (Opc.accessNonlocal, var. type, exit. pos);
          instr. Operand (var);
          instr. Operand (Address (exit. region, var, exit. pos));
          instr. Operand (store);
          opnd. ReplaceOperand (instr)

        | var: D.Struct DO
          (* procedure writes to a heap object of type `var' *)
          opnd. ReplaceOperand (var)
        END
      END SetExitOpnd;

    PROCEDURE AdjustOperands (call: D.Instruction; cinfo: CallInfo);
      VAR
        var: D.Addressable;
        attrib, opc: INTEGER;
        instr, enter: D.Instruction;
        opnd0: D.Opnd;
      BEGIN
        (* compare operands of `call' with results of `i. enter';
           move pointer to enter results to the first result that doesn't have
           a corresponding operand *)
        IF (i. enter # NIL) THEN
          opnd := call. NthOperand (3);
          res := i. enter. nextResult;

          (* skip formal parameters *)
          WHILE (res # NIL) &
                (res. location # NIL) &
                (res. location IS D.SymLocation) &
                (res. location(D.SymLocation). var IS D.Object) &
                (res. location(D.SymLocation). var(D.Object). localTo =
                                                            i. greg. bodyOf) DO
            opnd := opnd. nextOpnd;
            res := res. nextResult
          END;

          (* skip matching arguments *)
          WHILE (opnd # NIL) & (res # NIL) &
                SameLocation (opnd. location, res. location) DO
            IF Attr.PartOfStore (cinfo. caller, opnd. location) THEN
              INCL (cinfo. flags, readsFromStore)
            END;
            opnd := opnd. nextOpnd;
            res := res. nextResult
          END;

          (* for every following result `res' add a new operand to the call
             instruction *)
          WHILE (res # NIL) DO
            IF Attr.PartOfStore (cinfo. caller, res. location) THEN
              INCL (cinfo. flags, readsFromStore)
            END;
            
            var := res. location(D.SymLocation). var;
            WITH var: D.Object DO
              attrib := res. location(D.SymLocation). attrib;
              CASE attrib OF
              | D.symLocObject:
                IF (var = Sym.mem) THEN
                  (* no op *)
                  
                ELSIF (var. localTo = cinfo. caller) & 
                      (var. mode = D.objVar) THEN
                  (* reading local variable of the caller; get its value from
                     the list of collecting operands *)
                  opnd := cinfo. savedOpnds;
                  WHILE (opnd. location(D.SymLocation). var # var) OR
                        (opnd. location(D.SymLocation). attrib # D.symLocObject) DO
                    opnd := opnd. nextOpnd
                  END;
                  call. Operand (opnd. arg);
                  call. SetOpndSymLoc (var)
  
                ELSE (* reading from nonlocal variable or variable parameter *)
                  IF (var. mode = D.objVar) THEN
                    opc := Opc.accessNonlocal
                  ELSE
                    opc := Opc.accessVarParam
                  END;
                  instr := call. region. CreateInstruction (opc, var. type, call. pos);
                  instr. Operand (var);
                  instr. Operand (Address (call. region, var, call. pos));
                  instr. Operand (cinfo. storeIn. arg);
                  call. Operand (instr);
                  call. SetOpndSymLoc (var)
                END
                
              | D.symLocAddress:
                call. Operand (Address (call. region, var, call. pos));
                opnd := call. LastOperand();
                opnd. location := res. location
                
              ELSE  (* length or type tag of nonlocal parameter *)
                enter := call. region. EnterInstr();
                call. Operand (enter. GetResult (var, attrib));
                opnd := call. LastOperand();
                opnd. location := res. location
              END
              
            | var: D.Struct DO
              (* called procedure reads from heap object of type `var' *)
              call. Operand (var);
              call. SetOpndSymLoc (var)
            END;
            res := res. nextResult
          END;

          IF (cinfo. memIn # NIL) & ~(doesReadMem IN i. flags) THEN
            (* called procedure doesn't read from $mem: get rid of the operand
               that takes the collect instruction for its argument *)
            opnd0 := call. GetOperand (Sym.mem, D.symLocObject);
            opnd0. DeleteOperand()
          END
        END
      END AdjustOperands;

    BEGIN
      (* for all calls to procedure `i' from within a registered procedure:
         add results to the call that correspond to operands of the exit
         instruction and remove result $mem (if possible *)
      use := i. greg. bodyOf. useList;
      WHILE (use # NIL) DO
        IF RegisteredCall (use. instr) &
           (use. instr. NthOperand (2) = use) THEN
          (* refers to the third operand of a call instruction, i.e. to the one
             that designates the called procedure; now test if this call is
             part of a registered procedure *)
          greg := use. Greg();
          IF (greg. info # NIL) & (greg. info IS ProcInfo) THEN
            (* adjust result list of call to the completed exit instruction *)
            AdjustResults (use. instr, use. instr. info(CallInfo));
            (* if the called procedure `i' may raise an exception, make sure
               that all calls to it are marked as `live' *)
            IF (isNotDead IN i. flags) THEN
              INCL (use. instr. flags, D.instrNotDead)
            END
          END
        END;
        use := use. nextUse
      END;

      (* set proper values for new operands of the exit instruction *)
      IF (i. exit # NIL) THEN
        store := NIL;
        opnd := i. exit. opndList;
        WHILE (opnd # NIL) DO
          IF (opnd. arg = D.constUndef) THEN
            IF (store = NIL) THEN
              store := GetFinalStore (i. greg)
            END;
            SetExitOpnd (i. exit, opnd, store)
          END;
          opnd := opnd. nextOpnd
        END
      END;

      (* for all calls to procedure `i' from within a registered procedure:
         add operands to the call that correspond to results of the enter
         instruction and remove operand $mem (if possible *)
      use := i. greg. bodyOf. useList;
      WHILE (use # NIL) DO
        IF (use. instr. info # NIL) & (use. instr. info IS CallInfo) THEN
          (* adjust result list of call to the completed exit instruction *)
          AdjustOperands (use. instr, use. instr. info(CallInfo))
        END;
        use := use. nextUse
      END;

      (* remove $mem-value from enter or exit instruction *)
      IF (markedReadMem IN i. flags) & ~(doesReadMem IN i. flags) THEN
        res := i. enter. GetResult (Sym.mem, D.symLocObject);
        (* preserve structural integrety by inserting a dummy value instead of
           the result *)
        res. ReplaceUses (D.constUndef);
        res. DeleteResult()
      END;
      IF (markedWriteMem IN i. flags) & ~(doesWriteMem IN i. flags) THEN
        opnd0 := i. exit. GetOperand (Sym.mem, D.symLocObject);
        opnd0. DeleteOperand()
      END
    END AdjustGSA;

  PROCEDURE RestoreLists (callee: ProcInfo; call: D.Instruction);
  (* Restore operand and result lists that were saved in the call's 
     info field.  If allowed discard collects and reclaims.  *)
    VAR
      cinfo: CallInfo;
      lastOpnd, opnd: D.Opnd;
      lastResult, res: D.Result;
    BEGIN
      cinfo := call. info(CallInfo);
      
      IF (doesWriteMem IN callee. flags) THEN
        lastResult := call. GetResult (Sym.mem, D.symLocObject);
        lastResult. MoveResultToEnd()
      ELSE
        lastResult := call. LastResult()
      END;
      D.TransferResultList (lastResult, cinfo. savedResults, TRUE);
      
      IF (doesReadMem IN callee. flags) THEN
        lastOpnd := call. GetOperand (Sym.mem, D.symLocObject);
        lastOpnd. MoveOperandToEnd()
      ELSE
        lastOpnd := call. LastOperand()
      END;
      D.TransferOperandList (lastOpnd, cinfo. savedOpnds, TRUE);
      
      IF ~(doesWriteMem IN callee. flags) THEN
        (* discard reclaiming results since call doesn't write to $mem *)
        WHILE (lastResult. nextResult # NIL) DO
          res := lastResult. nextResult;
          IF (writesToStore IN cinfo. flags) & 
             (res. location(D.SymLocation). var = Sym.store) THEN
            (* we aren't writing to $mem, but we do change the $store of the
               caller: keep this result *)
            lastResult := res
          ELSE
            opnd := call. GetOperand (res. location(D.SymLocation). var, D.symLocObject);
            res. ReplaceUses (opnd. arg);
            res. DeleteResult()
          END
        END
      END;
      
      IF ~(doesReadMem IN callee. flags) THEN
        (* discard collecting operands since call doesn't read from $mem *)
        WHILE (lastOpnd. nextOpnd # NIL) DO
          opnd := lastOpnd. nextOpnd;
          IF (cinfo. flags * {readsFromStore, writesToStore} # {}) &
             (opnd. location(D.SymLocation). var = Sym.store) THEN
            (* we aren't reading from $mem, but we do read from or write to the
               $store of the caller: keep this operand *)
            lastOpnd := opnd
          ELSE
            lastOpnd. nextOpnd. DeleteOperand()
          END
        END
      END
    END RestoreLists;
  
  BEGIN
    (* create reverse call graph; determine which procedures read/write
       directly from/to $mem *)
    i := gregList;
    WHILE (i # NIL) DO
      ExamineInstructions (i, i. greg);
      i := i. next
    END;

    (* determine side-effects (read or write) for all registered procedures
       and change their enter and exit instructions accordingly *)
    PropagateSideEffects;
    PropagateMem;

    (* adjust code to new enter/exit instructions: for every call from within
       a registered procedure update its input operand and output results to
       the modified enter/exit instructions *)
    i := gregList;
    WHILE (i # NIL) DO
      IF (markedReadMem IN i. flags) THEN
        res0 := i. enter. GetResult (Sym.mem, D.symLocObject);
        res0. MoveResultToEnd()
      END;
      IF (markedWriteMem IN i. flags) THEN
        opnd0 := i. exit. GetOperand (Sym.mem, D.symLocObject);
        opnd0. MoveOperandToEnd()
      END;
      AdjustGSA (i);
      i := i. next
    END;

    (* cleanup: remove all references to the auxiliary data that was installed
       previously; reinstall the contents of `greg.info' that were valid before
       the call to `AddProc' *)
    WHILE (gregList # NIL) DO
(*      IF (doesReadMem IN gregList. flags) THEN
        D.MoveResultToEnd (D.FindResult (gregList. enter, 
                                         Sym.mem, D.symLocObject))
      END;
      IF (doesWriteMem IN gregList. flags) THEN
        D.MoveOperandToEnd (D.FindOperand (gregList. exit, 
                                           Sym.mem, D.symLocObject))
      END;
*)      
      use := gregList. greg. bodyOf. useList;
      WHILE (use # NIL) DO
        IF (use. instr. info # NIL) & (use. instr. info IS CallInfo) THEN
          RestoreLists (gregList, use. instr);
          use. instr. info := NIL
        END;
        use := use. nextUse
      END;
      gregList. greg. info := gregList. greg. info(ProcInfo). oldInfo;

      gregList := gregList. next
    END
  END Adjust;

BEGIN
  gregList := NIL
END SideEffects.
