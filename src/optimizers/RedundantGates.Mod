MODULE RedundantGates;
(*  Remove unnecessary gate instructions.
    
    Copyright (C) 1996  Juergen Zimmermann

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
  D := Data, Opc := Opcode;

PROCEDURE Eliminate* (reg: D.Region);
(* Scan region `reg' for unnecessary `gate' instruction and replace them
   by their argument. `gate' instructions are unnecessary, if all operands 
   (except for the first one, the `merge' instruction) are the same or if
   a gate belongs to a loop-merge and the third operand is `gate' itself.
   Unnecessary `gates' will be deleted. *)
  VAR
    changed: BOOLEAN;
  
  PROCEDURE ReplaceGate (gate: D.Instruction);
    VAR
      merge: D.Merge;
      opnd: D.Opnd;
      res: D.Usable;
      replace: BOOLEAN;
    BEGIN
      merge := gate. opndList. arg(D.Merge);
      opnd := gate. opndList. nextOpnd;
      res := opnd. arg;
      replace := (merge. opcode = Opc.mergeLoop) & (opnd. nextOpnd. arg = gate); (* gate evaluates to itself at loop back-edge *)       
      WHILE (opnd # NIL) & (opnd. arg = res) DO
        opnd := opnd. nextOpnd;
      END;
      IF (opnd = NIL) OR replace THEN
        D.ReplaceUses (gate, res);
        changed := TRUE;
        D.Delete (gate);
      END;
    END ReplaceGate;

  PROCEDURE ReplaceRegionGates (reg: D.Region);
    VAR
      instr, nextInstr: D.Instruction;
    BEGIN
      instr := reg. instrList;
      WHILE (instr # NIL) DO
        nextInstr := instr. nextInstr;
        IF (instr. opcode = Opc.gate) THEN
          ReplaceGate (instr);
        ELSIF (instr IS D.Region) THEN
          ReplaceRegionGates (instr(D.Region));
        END;
        instr := nextInstr;
      END; 
    END ReplaceRegionGates;

  BEGIN
    REPEAT
      changed := FALSE;
      ReplaceRegionGates (reg);
    UNTIL ~changed;
  END Eliminate;

END RedundantGates.

