(* 	$Id: DeadCodeElimination.Mod,v 1.10 1999/03/15 18:54:49 acken Exp $	 *)
MODULE DeadCodeElimination;
(*  Removes all unused instructions from GSA code.
    Copyright (C) 1995, 1996  Michael van Acken

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


CONST
  dead = 0;
  live = 1;


PROCEDURE MarkDead (instr: D.Instruction);
(* Marks instruction `instr' and all instructions that are nested in it as
   dead.  *)
  BEGIN
    instr. marker := dead;
    IF (instr IS D.Region) THEN          (* traverse instructions in region *)
      instr := instr(D.Region). instrList;
      WHILE (instr # NIL) DO
        MarkDead (instr);
        instr := instr. nextInstr
      END
    END
  END MarkDead;

PROCEDURE MarkLive (instr: D.Instruction);
(* Marks the instruction `instr' and all its operands as alive.  *)
  VAR
    opnd: D.Opnd;
  BEGIN
    IF (instr # NIL) & (instr. marker = dead) THEN
      instr. marker := live;
      MarkLive (instr. region);
      (* mark instructions that are used in the operands as alive *)
      opnd := instr. opndList;
      WHILE (opnd # NIL) DO
        IF (opnd. arg IS D.Result) THEN
          MarkLive (opnd. arg(D.Result). instr)
        END;
        opnd := opnd. nextOpnd
      END
    END
  END MarkLive;

PROCEDURE MarkException (instr: D.Instruction; removeDisabled: BOOLEAN);
(* Mark `instr' and all instructions nested in it that may raise an exception 
   as alive.  *)
  BEGIN
    IF (D.instrNotDead IN instr. flags) &
       ~((D.instrIsDisabled IN instr. flags) & removeDisabled) THEN
      MarkLive (instr)
    END;
    IF (instr IS D.Region) THEN          (* traverse instructions in region *)
      instr := instr(D.Region). instrList;
      WHILE (instr # NIL) DO
        MarkException (instr, removeDisabled);
        instr := instr. nextInstr
      END
    END
  END MarkException;

PROCEDURE DeleteDeadCode (instr: D.Instruction);
(* Deletes instruction `instr' if it is marked as dead.  If it's alive and
   happens to be a region, then all instructions nested in `instr' are searched
   for dead code.  *)
  VAR
    nextInstr: D.Instruction;
  BEGIN
    IF (instr. marker = dead) THEN
      instr. Delete()
    ELSIF (instr IS D.Region) THEN
      instr := instr(D.Region). instrList;
      WHILE (instr # NIL) DO
        nextInstr := instr. nextInstr;
        DeleteDeadCode (instr);
        instr := nextInstr
      END
    END
  END DeleteDeadCode;

PROCEDURE RemoveRuntimeChecks (region: D.Region);
(* Removes disabled runtime checks bound-index, bound-range, type-guard, and 
   type-assert from `region'.  They are replaced by their first operand.  *)
  VAR
    instr: D.Instruction;
    opc: INTEGER;
  BEGIN
    instr := region. instrList;
    WHILE (instr # NIL) DO
      WITH instr: D.Region DO
        RemoveRuntimeChecks (instr)
      ELSE
        opc := instr. opcode;
        IF (D.instrIsDisabled IN instr. flags) &
           ((opc = Opc.boundIndex) OR (opc = Opc.boundRange) OR 
            (opc = Opc.typeGuard) OR (opc = Opc.typeAssert)) THEN
          instr. ReplaceUses (instr. opndList. arg)
        END
      END;
      instr := instr. nextInstr
    END
  END RemoveRuntimeChecks;

PROCEDURE Eliminate* (greg: D.Region; removeDisabled: BOOLEAN);
(* Removes all instructions from a procedure's or module's code that do not 
   contribute to its result (i.e. to the operands of the exit instruction) and 
   that won't raise an exception (ie that haven't set the `instrNotDead' flag).
   Instructions that have the `instrIsDisabled' flag set are only removed if
   they are dead and `removeDisabled=TRUE' (in this case the `instrNotDead' 
   flag is ignored).
   Note that greg's enter and exit instructions are never deleted.  *)
  BEGIN
    IF removeDisabled THEN
      RemoveRuntimeChecks (greg)
    END;
    (* mark all instructions nested in `greg' as dead *)
    MarkDead (greg);
    (* mark enter and exit instruction as alive *)
    MarkLive (greg. EnterInstr());
    MarkLive (greg. ExitInstr());
    (* mark instructions that may raise an exception as alive *)
    MarkException (greg, removeDisabled);
    (* remove all instructions marked as dead *)
    DeleteDeadCode (greg)
  END Eliminate;

END DeadCodeElimination.
