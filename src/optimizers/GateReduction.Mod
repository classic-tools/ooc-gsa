(*	$Id: GateReduction.Mod,v 1.11 1999/03/15 18:54:21 acken Exp $	*)
MODULE GateReduction;
(*  Uses control flow information to simplify references to gate values.
    Copyright (C) 1995, 1996, 1997, 1998  Michael van Acken

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

(* This module is intended to straighten out some of the erratic data flow 
   caused by nonlocal exits like EXIT, RETURN, and traps.  *)


IMPORT
  D := Data, Opc := Opcode, Cond := GuardCond, Sym := SymbolTable;
  
PROCEDURE Reduce* (r: D.Region);
(* Tries to simplify uses of gates in `r' by replacing the use of the 
   whole gate by one of the gate operands.  
   pre: `GuardCond.Init' has been run beforehand and the information it adds to
        regions is still valid.  *)
  
  PROCEDURE TraverseGates (r: D.Region);
    VAR
      use, nextUse: D.Opnd;
      instr, new: D.Instruction;
      value: D.Usable;
      negate: BOOLEAN;
      negRegion: D.Region;
      pos: LONGINT;
      
    PROCEDURE VisibleValue (gate: D.Instruction; opnd: D.Opnd): D.Usable;
    (* Given a gate and use of this gate.  Determine if only one particular 
       argument of the gate will ever reach `opnd'.  If this can be proven, 
       return the value, otherwise return NIL (meaning that the gate has to be
       used as is).  *)
      VAR
        deepValue, shallowValue, opndValue: D.Usable;
        deepValid, shallowValid: BOOLEAN;
        opndInfo: Cond.RegionInfo;
        gateOpnd: D.Opnd;
      BEGIN
        IF (gate. opndList. arg(D.Merge). opcode = Opc.mergeLoop) THEN
          (* this is a loop gate; it has to be treated specially due to its
             recursive nature *)
          IF (gate. opndList. nextOpnd. nextOpnd. arg = gate) OR
             (gate. opndList. nextOpnd. arg = 
              gate. opndList. nextOpnd. nextOpnd. arg) THEN
            (* the backedge operand of the gate is the gate itself or both 
               operands are identical; this means that the gate always takes on
               the value of the operand that holds the value that is valid when
               entering the loop *)
            opndValue := gate. opndList. nextOpnd. arg;
            IF (opndValue IS D.Instruction) &
               (opndValue(D.Instruction). opcode = Opc.gate) THEN
              deepValue := VisibleValue (opndValue(D.Instruction), opnd);
              IF (deepValue # NIL) THEN
                RETURN deepValue
              END
            END;
            RETURN opndValue
          ELSE
            (* assume that all other loop gate will return two different 
               values *)
            RETURN NIL
          END
          
        ELSE
          deepValue := NIL; deepValid := TRUE;
          shallowValue := NIL; shallowValid := TRUE;
          opndInfo := Cond.OperandInfo (opnd);
          gateOpnd := gate. opndList. nextOpnd;
          WHILE (gateOpnd # NIL) DO
            IF ~Cond.Contradicting (Cond.OperandInfo (gateOpnd), opndInfo) THEN
              opndValue := gateOpnd. arg;
              IF (shallowValue = NIL) THEN
                shallowValue := opndValue
              ELSIF (shallowValue # opndValue) THEN
                shallowValid := FALSE
              END;
              
              IF (opndValue IS D.Instruction) &
                 (opndValue(D.Instruction). opcode = Opc.gate) THEN
                opndValue := VisibleValue (opndValue(D.Instruction), opnd);
                IF (opndValue = NIL) THEN  (* set variable to gate again *)
                  opndValue := gateOpnd. arg
                END
              END;
              IF (deepValue = NIL) THEN
                deepValue := opndValue
              ELSIF (deepValue # opndValue) THEN
                deepValid := FALSE
              END
            END;
            gateOpnd := gateOpnd. nextOpnd
          END;
          
          IF deepValid & (deepValue # NIL) THEN
            RETURN deepValue             (* return one of the gate values *)
          ELSIF shallowValid THEN
            RETURN shallowValue          (* return one of the gate operands *)
          ELSE
            RETURN NIL
          END
        END
      END VisibleValue;
    
    PROCEDURE CanReplace (use: D.Opnd; value: D.Usable): BOOLEAN;
      BEGIN
        (* the three variants of the procedure, sorted by increasing register 
           pressure (for the oo2c back-end):
             1) ~(value IS D.Result) OR Dominates (value.region, use.region)
             2) ~(value IS D.Result)
             3) TRUE
             4) FALSE
           The first alternative is implemented.  Note that the third may 
           cause problems when eliminating unreachable code, since a region
           may have life results at its end that aren't passed through gates *)
        WITH value: D.Result DO
          RETURN value. instr. region. Dominates (use. instr. region)
        ELSE
          RETURN TRUE
        END
      END CanReplace;
    
    PROCEDURE MergeGate (u: D.Usable): BOOLEAN;
      BEGIN
        WITH u: D.Gate DO
          RETURN (u. region(D.Merge). opcode # Opc.mergeLoop)
        ELSE
          RETURN FALSE
        END
      END MergeGate;
    
    BEGIN
      instr := r. instrList;
      WHILE (instr # NIL) DO
        IF (instr. opcode = Opc.gate) THEN
          (* try to replace use of gate by one of its operands *)
          use := instr. useList;
          WHILE (use # NIL) DO
            nextUse := use. nextUse;
            value := VisibleValue (instr, use);
            IF (value # NIL) & CanReplace (use, value) THEN
              use. ReplaceOperand (value)
            END;
            use := nextUse
          END;
          negate := Cond.TraceValue (instr, value, TRUE);
          IF (value # instr) & (instr. type # NIL) & 
             (instr. type. form = D.strBoolean) & 
             ~(negate & MergeGate (value)) &
             ((value IS D.Const) OR (value IS D.Object) OR 
              ~(negate & 
                (value(D.Result). instr. opndList # NIL) &
                (value(D.Result). instr. opndList. arg = instr))) THEN
            (* replace gate by reference `[~]value', unless the obsolete 
               instruction happens to be a mere negation, or we would be
               forced to place a negation intruction in a non-loop merge *)
            IF negate THEN  (* add boolean negation *)
              IF (value IS D.Const) THEN  (* value is `TRUE' *)
                value := Sym.constFalse
              ELSE
                IF (value IS D.Object) THEN
                  (* negating undefined value, using global region to place the not *)
                  negRegion := r. Greg();
                  pos := instr. pos
                ELSE
                  negRegion := value(D.Result). instr. region;
                  pos := value(D.Result). instr. pos
                END;
                new := negRegion. CreateInstruction (Opc.notsu, D.struct[D.strBoolean], pos);
                new. Operand (value);
                value := new
              END
            END;
            instr. ReplaceUses (value)
          END
        ELSIF (instr IS D.Region) THEN
          TraverseGates (instr(D.Region))
        END;
        instr := instr. nextInstr
      END
    END TraverseGates;
  
  BEGIN
    r. ClearInstrInfo (0);
    r(D.GlobalRegion). NumberDominanceTree();
    TraverseGates (r)
  END Reduce;

END GateReduction.
