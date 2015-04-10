(*	$Id: GuardPropagation.Mod,v 1.5 1999/03/19 20:39:00 acken Exp $	*)
MODULE GuardPropagation;
(*  Uses the knowledge that a guard holds to transform code in the range
    of the guard that uses the guarded value.
    Copyright (C) 1996  Michael van Acken

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
  D := Data, Opc := Opcode, Sym := SymbolTable, Cond := GuardCond;
  

(* 
The idea is to replace all occurences of a value that is known to hold, or
not to hold, by either TRUE or FALSE.  A guard determines if its operand holds
or not.  All instructions that are nested in this guard `know' what value the
guard operand has.  If the guard is `if-true: a', the `a' holds inside the 
guard, and vice versa for `if-false:'.  

Effects of running `Propagate':
* `a & a' and `a OR a' turn into `a' (if GateReduction is run afterwards), 
  the other boolean contructs like `a & ~a', `a OR ~a' etc are also transformed
  properly
* for the range of a guard `a = c' or `c = a', where `c' is a constant, all
  occurences of `a' are replaced by `c'
*)

PROCEDURE Dominates (reg0, reg1: D.Region): BOOLEAN;
(* TRUE iff region `reg0' dominates region `reg1', ie, if every path from the 
   top-most region greg to `reg1' includes `reg0'.  *)
  BEGIN
    WHILE (reg1 # NIL) & (reg0 # reg1) DO
      reg1 := reg1. region
    END;
    RETURN (reg1 # NIL)
  END Dominates;

PROCEDURE Propagate* (greg: D.Region);
(* ...
   Should be run before `GateReduction.Reduce'.
   pre: `GuardCond.Init' has been run beforehand and the information it adds to
        the instructions and regions is still valid.  *)
  VAR
    s: Cond.RegionSummary;
    regionCount, i: INTEGER;
    regionInfos: Cond.InfoArray;
    regionMatrix: Cond.RegionMatrix;
    r: D.Region;
    arg: D.Usable;
    instr: D.Instruction;
  
  PROCEDURE CanBeModified (guard: D.Region; opnd: D.Opnd): BOOLEAN;
    BEGIN
      IF (opnd. instr IS D.Guard) THEN
        RETURN Dominates (guard, opnd. instr(D.Region))
      ELSE
        RETURN opnd. ValueOperand()
      END
    END CanBeModified;
  
  PROCEDURE ReplaceBoolUses (guard: D.Region; value: D.Usable; replaceWith: BOOLEAN);
    VAR
      use, next: D.Opnd;
    BEGIN
      use := value. useList;
      WHILE (use # NIL) DO
        next := use. nextUse;
        IF Cond.Implication (Cond.OperandInfo (use), guard. info(Cond.RegionInfo)) &
           CanBeModified (guard, use) THEN
          IF replaceWith THEN
            use. ReplaceOperand (Sym.constTrue)
          ELSE
            use. ReplaceOperand (Sym.constFalse)
          END;
          IF (use. instr. opcode = Opc.copy) THEN
            ReplaceBoolUses (guard, use. instr, replaceWith)
          ELSIF (use. instr. opcode = Opc.notsu) THEN
            ReplaceBoolUses (guard, use. instr, ~replaceWith)
          END
        END;
        use := next
      END
    END ReplaceBoolUses;
  
  PROCEDURE ReplaceUses (guard: D.Region; value: D.Usable; replaceWith: D.Usable);
    VAR
      use, next: D.Opnd;
    BEGIN
      IF ~(value IS D.Const) THEN
        use := value. useList;
        WHILE (use # NIL) DO
          next := use. nextUse;
          IF Cond.Implication (Cond.OperandInfo (use), guard. info(Cond.RegionInfo)) &
             CanBeModified (guard, use) THEN
            use. ReplaceOperand (replaceWith)
          END;
          use := next
        END
      END
    END ReplaceUses;
  
  BEGIN
    s := greg. info(Cond.RegionInfo). summary;
    regionCount := s. count; regionInfos := s. infos; regionMatrix := s. matrix;
    
    FOR i := 0 TO regionCount-1 DO
      r := regionInfos[i]. region;
      IF ~Cond.Unreachable (r) &
         ((r. opcode = Opc.guardTrue) OR (r. opcode = Opc.guardFalse)) &
         ~(r. opndList. arg IS D.Const) THEN
        arg := r. opndList. arg;
        (* replace uses of guard operand *)
        ReplaceBoolUses (r, r. opndList. arg, r. opcode = Opc.guardTrue);

        IF (arg IS D.Instruction) THEN
          instr := arg(D.Instruction);
          
          IF (r. opcode = Opc.guardTrue) &
               (instr. opcode DIV Opc.sizeClass = Opc.classEql) &
               (instr. opcode # Opc.eqlstr) OR
             (r. opcode = Opc.guardFalse) &
               (instr. opcode DIV Opc.sizeClass = Opc.classNeq) &
               (instr. opcode # Opc.neqstr) THEN
            (* if the equation has a constant part, then replace uses of non-
               constant side of equation by the constant one *)
            IF (instr. opndList. arg IS D.Const) THEN
              ReplaceUses (r, instr. opndList. nextOpnd. arg, 
                              instr. opndList. arg)
            ELSIF (instr. opndList. nextOpnd. arg IS D.Const) THEN
              ReplaceUses (r, instr. opndList. arg, 
                              instr. opndList. nextOpnd. arg)
            END
          END
        END
      END
    END
  END Propagate;

END GuardPropagation.
