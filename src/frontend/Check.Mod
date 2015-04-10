(*	$Id: Check.Mod,v 1.18 1999/07/30 21:10:20 acken Exp $	*)
MODULE Check;
(*  Consistency checks on GSA level.
    Copyright (C) 1997-1999  Michael van Acken

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

(* This module provides procedures to assert that certain invariants of the GSA
   code representation still hold after a transformation.  
   Violations are marked with the pseudo position `WriteGSA.mark'.  They are 
   marked with [XXX] in the written GSA code.  *)

IMPORT
(*  Types,*)
  SYSTEM, Out, D := Data, Opc := Opcode, Sym := SymbolTable, WriteGSA;
  
  
PROCEDURE Error (VAR ok: BOOLEAN; msg: ARRAY OF CHAR);
  BEGIN
    Out.String ("Check failed: ");
    Out.String (msg);
    Out.Ln;
    Out.String ("The offending operand or instruction is marked with [XXX]");
    Out.Ln;
    ok := FALSE
  END Error;


PROCEDURE WrType* (o: SYSTEM.PTR);
(*
  VAR
    t: Types.Type;
  BEGIN
    t := Types.TypeOf (o);
    Out.String (t. module. name);
    Out.Char (".");
    Out.String (t. name);
    Out.Ln
*)    
  END WrType;


PROCEDURE GuardUses* (r: D.Region): BOOLEAN;
(* All uses of a guard have to be merges.  A guard can be the `enclosing' 
   operand of arbitrary loop merges, plus, optionally, the `backedge' operand
   of a single loop merge, or the operand of a single if or cond merge.  No
   operand of the guard is the guard itself.  *)
  VAR
    ok: BOOLEAN;
    other: INTEGER;
    use: D.Opnd;
  BEGIN
    ok := TRUE;
    IF (r IS D.Guard) THEN
      other := 0;
      use := r. useList;
      WHILE (use # NIL) DO
        IF (use. instr = r) THEN
          Error (ok, "Guard has itself as operand");
          r. pos := WriteGSA.mark
        END;
        IF ~(use. instr IS D.Merge) THEN
          Error (ok, "Guard is operand of something other than Merge");
          r. pos := WriteGSA.mark
        END;
        IF ~((use. instr. opcode = Opc.mergeLoop) &
             (use. instr. opndList. arg = r)) OR
           (use. instr. region # r) THEN
          INC (other);
          IF (other # 1) THEN
            Error (ok, "Guard has more than one (non-loop) use");
            r. pos := WriteGSA.mark
          END
        END;
        use := use. nextUse
      END
    END;
    
    r := r. regionList;
    WHILE (r # NIL) DO
      ok := GuardUses (r) & ok;
      r := r. nextRegion
    END;
    
    RETURN ok
  END GuardUses;

PROCEDURE MergeUses* (r: D.Region): BOOLEAN;
(* All uses of a loop merge have to be loop merges (except for gates).  No 
   operand of a merge is the merge itself (except, possibly, loop merges that
   never terminate).  The uses of a gate are either gates, loop merges, plus
   optionally one merge operand that isn't a loop merge.  A merge can be the 
   `enclosing' operand of arbitrary loop merges, plus, optionally, the 
   `backedge' operand of a single loop merge, or the operand of a single if 
   or cond merge.  *)
  VAR
    ok: BOOLEAN;
    use: D.Opnd;
    other: INTEGER;
  BEGIN
    ok := TRUE;
    IF (r IS D.Merge) THEN
      other := 0;
      use := r. useList;
      WHILE (use # NIL) DO
        IF (use. instr = r) &
           ((r. opcode # Opc.mergeLoop) OR (use. nextOpnd # NIL)) THEN
          Error (ok, "Merge has itself as operand");
          r. pos := WriteGSA.mark
        END;
        IF (use. instr. opcode # Opc.gate) THEN
          IF (r. opcode = Opc.mergeLoop) &
             (use. instr. opcode # Opc.mergeLoop) THEN
            Error (ok, "Loop merge is operand of something other than a loop merge");
            r. pos := WriteGSA.mark
          END;
          IF ~(use. instr IS D.Merge) THEN
            Error (ok, "Merge is operand of something other than Gate or Merge");
            r. pos := WriteGSA.mark
          ELSIF ~((use. instr. opcode = Opc.mergeLoop) &
                  (use. instr. opndList. arg = r)) THEN
            INC (other);
            IF (other # 1) THEN
              Error (ok, "Merge has more than one (non-loop) use");
              r. pos := WriteGSA.mark
            END
          END
        END;
        use := use. nextUse
      END
    END;
    
    r := r. regionList;
    WHILE (r # NIL) DO
      ok := MergeUses (r) & ok;
      r := r. nextRegion
    END;
    
    RETURN ok
  END MergeUses;

PROCEDURE GateOpnds (r: D.Region): BOOLEAN;
(* A gate has as operands its merge plus as many operands as the merge.  The
   merge has 2 operands (for if, loop, and cond merge), or at least 1 operand
   for case merges.  *)
  VAR
    ok: BOOLEAN;
    instr: D.Instruction;
    count: INTEGER;
    merge: D.Merge;
    gateOpnd, mergeOpnd: D.Opnd;
  BEGIN
    ok := TRUE;
    instr := r. instrList;
    WHILE (instr # NIL) DO
      IF (instr. opcode = Opc.gate) THEN
        IF (instr. opndList = NIL) THEN
          Error (ok, "Gate has no operand");
          instr. pos := WriteGSA.mark
        ELSIF ~(instr. opndList. arg IS D.Merge) THEN
          Error (ok, "First operand of Gate isn't a Merge");
          instr. pos := WriteGSA.mark
        ELSE
          merge := instr. opndList. arg(D.Merge);
          count := 0;
          gateOpnd := instr. opndList. nextOpnd;
          mergeOpnd := merge. opndList;
          WHILE (gateOpnd # NIL) & (mergeOpnd # NIL) DO
            gateOpnd := gateOpnd. nextOpnd;
            mergeOpnd := mergeOpnd. nextOpnd;
            INC (count)
          END;
          IF (gateOpnd = NIL) & (mergeOpnd # NIL) THEN
            Error (ok, "Gate has not enough operands");
            instr. pos := WriteGSA.mark
          ELSIF (gateOpnd # NIL) & (mergeOpnd = NIL) THEN
            Error (ok, "Gate has too many operands");
            instr. pos := WriteGSA.mark
          ELSE
            CASE merge. opcode OF
            | Opc.mergeIf, Opc.mergeCond, Opc.mergeLoop:
              IF (count # 2) THEN
                Error (ok, "Merge has illegal number of operands");
                merge. pos := WriteGSA.mark
              END
            | Opc.mergeCase:
              IF (count < 1) THEN
                Error (ok, "Merge has illegal number of operands");
                merge. pos := WriteGSA.mark
              END
            ELSE
              Error (ok, "First operand of gate has illegal opcode");
              instr. pos := WriteGSA.mark
            END
          END
        END
      ELSIF (instr IS D.Region) THEN
        ok := ok & GateOpnds (instr(D.Region))
      END;
      instr := instr. nextInstr
    END;
    RETURN ok
  END GateOpnds;

PROCEDURE Opnds (r: D.Region): BOOLEAN;
(* All results referenced by an operand have to originate from the same global
   regions.  An operand list contains at most one operand of $mem.  The same
   holds for $store.  If a $mem operand is present it is followed immediately
   by $store (except for exit instructions).  *)
  VAR
    ok: BOOLEAN;
    instr: D.Instruction;
    greg, region: D.Region;
    opnd, opndPtr: D.Opnd;
    source: D.Instruction;
  BEGIN
    greg := r. Greg();
    ok := TRUE;
    instr := r. instrList;
    WHILE (instr # NIL) DO
      opnd := instr. opndList;
      WHILE (opnd # NIL) DO
        IF (opnd. arg IS D.Result) THEN
          source := opnd. arg(D.Result). instr;
          region := source. region;
          IF (source # greg) & (region = NIL) THEN
            Error (ok, "Operand references deleted instruction");
            opnd. pos := WriteGSA.mark
          ELSIF (source # greg) & (region. Greg() # greg) THEN
            Error (ok, "Operand references foreign result");
            opnd. pos := WriteGSA.mark
          END
        END;
        opnd := opnd. nextOpnd
      END;
      
      opnd := instr. GetOperand (Sym.store, D.symLocObject);
      IF (opnd # NIL) THEN
        opndPtr := opnd. nextOpnd;
        WHILE (opndPtr # NIL) DO
          IF (opndPtr. location # NIL) & (opndPtr. location IS D.SymLocation) &
             (opndPtr. location(D.SymLocation). var = Sym.store) THEN
            Error (ok, "Two $store operands");
            opnd. pos := WriteGSA.mark
          END;
          opndPtr := opndPtr. nextOpnd
        END
      END;
      
      opnd := instr. GetOperand (Sym.mem, D.symLocObject);
      IF (opnd # NIL) THEN
        opndPtr := opnd. nextOpnd;
        WHILE (opndPtr # NIL) DO
          IF (opndPtr. location # NIL) & (opndPtr. location IS D.SymLocation) &
             (opndPtr. location(D.SymLocation). var = Sym.mem) THEN
            Error (ok, "Two $mem operands");
            opnd. pos := WriteGSA.mark
          END;
          opndPtr := opndPtr. nextOpnd
        END;
        
        IF (instr. opcode # Opc.exit) &
           ((opnd. nextOpnd = NIL) OR
            (opnd. nextOpnd # instr. GetOperand (Sym.store, D.symLocObject))) THEN
          Error (ok, "Operand $store has to follow $mem");
          opnd. pos := WriteGSA.mark
        END
      END;
      
      IF (instr IS D.Region) THEN
        ok := ok & Opnds (instr(D.Region))
      END;
      instr := instr. nextInstr
    END;
    RETURN ok
  END Opnds;

PROCEDURE Results (r: D.Region): BOOLEAN;
(* An result list contains at most one result for $mem.  The same holds for 
   $store.  If a $mem result is present it is followed immediately by $store 
   (except for enter instructions).  If an instruction writes to $mem it also
   needs to read $mem.  The same holds for $store.  *)
  VAR
    ok: BOOLEAN;
    instr: D.Instruction;
    res, resPtr: D.Result;
  BEGIN
    ok := TRUE;
    instr := r. instrList;
    WHILE (instr # NIL) DO
      res := instr. GetResult (Sym.store, D.symLocObject);
      IF (res # NIL) THEN
        resPtr := res. nextResult;
        WHILE (resPtr # NIL) DO
          IF (resPtr. location # NIL) & (resPtr. location IS D.SymLocation) &
             (resPtr. location(D.SymLocation). var = Sym.store) THEN
            Error (ok, "Two $store results");
            instr. pos := WriteGSA.mark
          END;
          resPtr := resPtr. nextResult
        END;
        
        IF (instr. GetOperand (Sym.store, D.symLocObject) = NIL) THEN
          Error (ok, "Instruction writes to $store but doesn't read it");
          instr. pos := WriteGSA.mark
        END
      END;
      
      res := instr. GetResult (Sym.mem, D.symLocObject);
      IF (res # NIL) THEN
        resPtr := res. nextResult;
        WHILE (resPtr # NIL) DO
          IF (resPtr. location # NIL) & (resPtr. location IS D.SymLocation) &
             (resPtr. location(D.SymLocation). var = Sym.mem) THEN
            Error (ok, "Two $mem results");
            instr. pos := WriteGSA.mark
          END;
          resPtr := resPtr. nextResult
        END;
        
        IF (instr. GetOperand (Sym.mem, D.symLocObject) = NIL) THEN
          Error (ok, "Instruction writes to $mem but doesn't read it");
          instr. pos := WriteGSA.mark
        END;
        
        IF (instr. opcode # Opc.enter) &
           ((res. nextResult = NIL) OR
            (res. nextResult # instr. GetResult (Sym.store, D.symLocObject))) THEN
          Error (ok, "Result $store has to follow $mem");
          instr. pos := WriteGSA.mark
        END
      END;
      
      IF (instr IS D.Region) THEN
        ok := ok & Results (instr(D.Region))
      END;
      instr := instr. nextInstr
    END;
    RETURN ok
  END Results;

PROCEDURE Enter (greg: D.Region): BOOLEAN;
(* For every greg an enter instruction exists.  The exit instruction may be 
   missing, e.g. for function procedures that have no RETURN.  If an enter
   has a $mem result it is at the very end of the result list.  An enter cannot
   contain a $store result.  *)
  VAR
    ok: BOOLEAN;
    instr: D.Instruction;
    res: D.Result;
  BEGIN
    ok := TRUE;
    instr := greg. EnterInstr();
    IF (instr = NIL) THEN
      Error (ok, "Missing enter instruction");
      greg. pos := WriteGSA.mark
    ELSE
      res := instr. GetResult (Sym.mem, D.symLocObject);
      IF (res # NIL) & (res. nextResult # NIL) THEN
        Error (ok, "Enter has $mem, but not at end of result list");
        greg. pos := WriteGSA.mark
      END;
      res := instr. GetResult (Sym.store, D.symLocObject);
      IF (res # NIL) THEN
        Error (ok, "Enter has $store result");
        greg. pos := WriteGSA.mark
      END
    END;
    RETURN ok
  END Enter;

PROCEDURE Exit (greg: D.Region): BOOLEAN;
(* If an exit has a $mem operand it is at the very end of the operand list.  In
   this case the enter instruction has to have a $mem result.  An exit cannot 
   have a $store operand.  *)
  VAR
    ok: BOOLEAN;
    instr, enter: D.Instruction;
    opnd: D.Opnd;
    res: D.Result;
  BEGIN
    ok := TRUE;
    instr := greg. ExitInstr();
    IF (instr # NIL) THEN
      opnd := instr. GetOperand (Sym.mem, D.symLocObject);
      IF (opnd # NIL) THEN
        IF (opnd. nextOpnd # NIL) THEN
          Error (ok, "Exit has $mem, but not at end of operand list");
          greg. pos := WriteGSA.mark
        END;
        enter := greg. EnterInstr();
        res := enter. GetResult (Sym.mem, D.symLocObject);
        IF (res = NIL) THEN
          Error (ok, "Exit has $mem, but enter hasn't");
          instr. pos := WriteGSA.mark
        END
      END;
      
      opnd := instr. GetOperand (Sym.store, D.symLocObject);
      IF (opnd # NIL) THEN
        Error (ok, "Exit has $store operand");
        greg. pos := WriteGSA.mark
      END
    END;
    RETURN ok
  END Exit;

PROCEDURE LoopGates (r: D.Region): BOOLEAN;
(* The second argument of a loop gate (the one that corresponds to the loop's
   entry edge) is calculated outside the loop.  Since the access rules for 
   structured values differs somewhat from the ones for scalar ones, this is
   only checked for gates of unstructured values.  *)
  VAR
    ok: BOOLEAN;
    instr: D.Instruction;
    merge: D.Merge;
    gateOpnd: D.Opnd;
    region: D.Region;
  BEGIN
    ok := TRUE;
    instr := r. instrList;
    WHILE (instr # NIL) DO
      IF (instr. opcode = Opc.gate) & 
         (instr. opndList. arg(D.Merge). opcode = Opc.mergeLoop) THEN
        merge := instr. opndList. arg(D.Merge);
        gateOpnd := instr. opndList. nextOpnd;
        IF ((instr. type = NIL) OR ~Sym.TypeInGroup (instr. type, D.grpStructured)) &
           (gateOpnd. arg IS D.Result) THEN
          region := gateOpnd. arg(D.Result). instr. region;
          WHILE (region # NIL) & (region # merge) DO
            region := region. region
          END;
          IF (region = merge) THEN
            Error (ok, "Second argument of loop gate calculated inside loop");
            gateOpnd. pos := WriteGSA.mark
          END
        END
      END;
      IF (instr IS D.Region) THEN
        ok := ok & LoopGates (instr(D.Region))
      END;
      instr := instr. nextInstr
    END;
    RETURN ok
  END LoopGates;

PROCEDURE Update (r: D.Region): BOOLEAN;
(* For an update instruction whose last argument A is of a _structured_ value,
   one of the following conditions holds:
   a) A is an update-element, update-field, struct-copy, or string-copy 
      instruction, or
   b) A is an access instruction
   c) the update instruction updates $store after a procedure call, i.e. A is
      a result of a call or a reclaim instruction *)
  VAR
    ok: BOOLEAN;
    instr: D.Instruction;
    opnd: D.Opnd;
  BEGIN
    ok := TRUE;
    instr := r. instrList;
    WHILE (instr # NIL) DO
      IF (instr. opcode DIV Opc.sizeClass = Opc.classUpdate) THEN
        IF (instr. opcode = Opc.updateMem) THEN
          opnd := instr. NthOperand (1)
        ELSE
          opnd := instr. LastOperand()
        END;
        IF Sym.TypeInGroup (opnd. OpndType(), D.grpStructured) THEN
          (* we got an update instruction that "writes" a structured value *)
          IF (opnd. arg IS D.Instruction) &
             ((opnd. arg(D.Instruction). opcode = Opc.updateElement) OR
              (opnd. arg(D.Instruction). opcode = Opc.updateField)) THEN
            (* operand updates a record field or an array element *)
          ELSIF (opnd. arg IS D.Instruction) &
                ((opnd. arg(D.Instruction). opcode DIV Opc.sizeClass = 
                                                            Opc.classAccess) OR
                 (opnd. arg(D.Instruction). opcode = Opc.structCopy) OR
                 (opnd. arg(D.Instruction). opcode = Opc.stringCopy)) THEN
            (* structured assignment; a non-scalar value is copied as a memory
               block *)
          ELSIF ((instr. opcode = Opc.updateField) OR
                 (instr. opcode = Opc.updateElement)) &
                (opnd. arg IS D.Result) &
                (opnd. arg(D.Result). instr. opcode = Opc.call) THEN
            (* update registers a procedure's side-effect upon a variable 
               parameter *)
          ELSIF ((instr. opcode = Opc.updateNonlocal) OR
                 (instr. opcode = Opc.updateVarParam) OR
                 (instr. opcode = Opc.updateHeap)) &
                (opnd. arg IS D.Result) &
                (opnd. arg(D.Result). instr. opcode = Opc.call) THEN
            (* update registers a procedure's side-effect in $store or of a
               local variable (heap variable) of structured type *)
          ELSE
            Error (ok, "Invalid source of update argument");
            opnd. pos := WriteGSA.mark
          END
        END
      END;
      IF (instr IS D.Region) THEN
        ok := ok & Update (instr(D.Region))
      END;
      instr := instr. nextInstr
    END;
    RETURN ok
  END Update;

PROCEDURE Structure (r: D.Region): BOOLEAN;
(* Check structural consistency of region.  *)
  VAR
    ok: BOOLEAN;
    i: D.Instruction;
    res: D.Result;
    use, opnd: D.Opnd;
  
  PROCEDURE SameGreg (r0: D.Region; i: D.Instruction): BOOLEAN;
    VAR
      r1: D.Region;
    BEGIN
      WITH i: D.Region DO
        r1 := i
      ELSE
        r1 := i. region
      END;
      WHILE (r0. region # NIL) DO
        r0 := r0. region
      END;
      WHILE (r1. region # NIL) DO
        r1 := r1. region
      END;
      RETURN (r0 = r1)
    END SameGreg;
  
  BEGIN
    ok := TRUE;
    
    i := r. instrList;
    WHILE (i # NIL) DO
      IF (i. region # r) THEN
        Error (ok, "Structural error 1");
        i. pos := WriteGSA.mark
      END;
      
      res := i;
      WHILE (res # NIL) DO
        IF (res. instr # i) THEN
          Error (ok, "Structural error 2");
          i. pos := WriteGSA.mark
        END;
        use := res. useList;
        WHILE (use # NIL) DO
          IF (use. instr. region = NIL) THEN
            Error (ok, "Structural error 6");
            i. pos := WriteGSA.mark
          ELSIF ~SameGreg (r, use. instr) THEN
            Error (ok, "Structural error 3");
            i. pos := WriteGSA.mark
          END;
          use := use. nextUse
        END;
        res := res. nextResult
      END;
      
      opnd := i. opndList;
      WHILE (opnd # NIL) DO
        IF (opnd. instr # i) THEN
          Error (ok, "Structural error 4");
          opnd. pos := WriteGSA.mark
        ELSIF (opnd. arg IS D.Result) & 
              (opnd. arg(D.Result). instr. region = NIL) &
              (opnd. arg(D.Result). instr. opcode # Opc.guardGreg) THEN
          Error (ok, "Operand references deleted instruction");
          opnd. pos := WriteGSA.mark
        ELSIF (opnd. arg IS D.Result) & 
              ~SameGreg (r, opnd. arg(D.Result). instr) THEN
          Error (ok, "Structural error 5");
          opnd. pos := WriteGSA.mark
        END;
        opnd := opnd. nextOpnd
      END;
      
      IF (i IS D.Region) THEN
        ok := ok & Structure (i(D.Region))
      END;
      
      i := i. nextInstr
    END;
    RETURN ok
  END Structure;


PROCEDURE All* (r: D.GlobalRegion): BOOLEAN;
  VAR
    ok: BOOLEAN;
  BEGIN
    ok := Structure (r);
    ok := ok & GuardUses (r);
    ok := ok & MergeUses (r);
    ok := ok & GateOpnds (r);
    ok := ok & Opnds (r);
    ok := ok & Enter (r);
    ok := ok & Exit (r);
    ok := ok & LoopGates (r);
    ok := ok & Update (r);
    IF ~ok THEN
      WriteGSA.Body (r)
    END;
    RETURN ok
  END All;

END Check.
