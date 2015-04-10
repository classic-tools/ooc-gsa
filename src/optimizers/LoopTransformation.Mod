(*	$Id: LoopTransformation.Mod,v 1.6 1999/03/19 20:39:07 acken Exp $	*)
MODULE LoopTransformation;
(*  Loop invariant code motion.
    Copyright (C) 1996-1998  Michael van Acken

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

(* 
Note: Currently this module only does loop invariant code motion, the most
trivial of the loop transformations.  In particular reassociation and strength
reduction aren't implemented yet.  Any volunteers?
*)


IMPORT
  D := Data, Opc := Opcode, Worklist;
  
  
CONST  (* flags assigned to instruction of a loop *)
  loopInvariant = 0;
  forwardInductive = 1;
  other = 2;


PROCEDURE AnalyseLoop (loop: D.Region);
(* Classifies all top-level instructions of `loop' and all instructions nested
   in `loop' that aren't part of another loop as leither oop invariant, forward
   inductive, or other.  *)
  VAR
    instr: D.Instruction;
    iInstr: D.Info;
    opnd, use: D.Opnd;
    res: D.Result;
    newMarker, m1: LONGINT;
    worklist: Worklist.Worklist;
    
  PROCEDURE Category (opnd: D.Opnd): LONGINT;
  (* Returns category (loop invariant, forward inductive, or other) of the 
     given argument.  *)
    VAR
      arg: D.Usable;
      instr: D.Instruction;
      r: D.Region;
    BEGIN
      arg := opnd. arg;
      WITH arg: D.Const DO
        RETURN loopInvariant
      | arg: D.Object DO
        RETURN loopInvariant
      | arg: D.Struct DO
        RETURN loopInvariant
      | arg: D.Region DO
        RETURN other
      | arg: D.Result DO
        instr := arg. instr;
        IF (instr. region = loop) THEN
          RETURN instr. marker
        ELSIF loop. Dominates (instr. region) THEN
          r := instr. region;
          WHILE (r # loop) DO
            IF (r. opcode = Opc.mergeLoop) THEN
              (* instruction is part of another loop nested in `loop' *)
              RETURN other
            END;
            r := r. region
          END;
          RETURN instr. marker
        ELSE
          RETURN loopInvariant
        END
      END
    END Category;
  
  PROCEDURE FillWorklist (region: D.Region);
    VAR
      instr: D.Instruction;
    BEGIN
      IF (region = loop) OR (region. opcode #  Opc.mergeLoop) THEN
        instr := region. instrList;
        WHILE (instr # NIL) DO
          IF (instr IS D.Region) THEN
            FillWorklist (instr(D.Region))
          ELSE
            IF (D.instrUniqueResult IN instr. flags) THEN
              (* NEW instructions are never loop invariant, every invocation 
                 delivers another value; a similar argument holds for certain 
                 functions and procedures (like sleep(n)) that cannot be 
                 folded away  *)
              instr. marker := other
            ELSE
              worklist. AddTail (instr)
            END
          END;
          instr := instr. nextInstr
        END
      END
    END FillWorklist;
    
  PROCEDURE MarkedInstr (instr: D.Instruction): BOOLEAN;
  (* Returns TRUE if `instr' is part of the current loop and takes part in the
     marking process.  *)
    VAR
      r: D.Region;
    BEGIN
      IF (instr. region = loop) THEN
        RETURN TRUE
      ELSIF loop. Dominates (instr. region) THEN
        r := instr. region;
        WHILE (r # loop) DO
          IF (r. opcode = Opc.mergeLoop) THEN
            RETURN FALSE
          END;
          r := r. region
        END;
        RETURN TRUE
      ELSE
        RETURN FALSE
      END
    END MarkedInstr;
  
  BEGIN
    (* create worklist with all top-level instructions of `loop' *)
    worklist. Init;
    FillWorklist (loop);
    
    (* examine category of every instruction in `worklist' *)
    WHILE ~worklist. IsEmpty() DO
      (* fetch `instr' from `worklist' *)
      iInstr := worklist. GetHead ();
      worklist. RemoveHead;
      instr := iInstr(D.Instruction);
      
      (* compute marker of `instr' *)
      IF (instr IS D.Gate) THEN
        IF (instr. region = loop) THEN
          (* loop gate: category is `other' if the backedge operand is `other';
             otherwise it is `forward inductive'; note that the first operand
             is always loop invariant *)
          IF (Category (instr. opndList. nextOpnd. nextOpnd) = other) THEN
            newMarker := other
          ELSE
            newMarker := forwardInductive
          END
        ELSE
          (* all other gates from nested merges belong to `other' *)
          newMarker := other
        END
        
      ELSIF (instr. opcode DIV Opc.sizeClass = Opc.classAdd) OR
            (instr. opcode DIV Opc.sizeClass = Opc.classSub) THEN
        (* increment or decrement operation: category is the worst of both
           operands *)
        m1 := Category (instr. opndList);
        newMarker := Category (instr. opndList. nextOpnd);
        IF (m1 > newMarker) THEN
          newMarker := m1
        END
        
      ELSIF (instr. region # loop) &
            ((instr. opcode DIV Opc.sizeClass = Opc.classAccess) OR
             (instr. opcode DIV Opc.sizeClass = Opc.classUpdate) OR
             (instr. opcode = Opc.structCopy) OR
             (instr. opcode = Opc.stringCopy) OR
             instr. MayTrap()) THEN
        (* instructions from guards nested in `loop' have to be treated 
           specially; any instruction that might cause a run-time error can't
           be moved out of its guard without special precautions, because the
           guard might ensure that it will never be executed with invalid 
           input *)
        newMarker := other
        
      ELSE
        (* all other instructions are loop invariant unless one of their 
           arguments isn't loop invariant *)
        newMarker := loopInvariant;
        opnd := instr. opndList;
        WHILE (opnd # NIL) DO
          IF (Category (opnd) # loopInvariant) THEN
            newMarker := other
          END;
          opnd := opnd. nextOpnd
        END
      END;
      
      IF (newMarker # instr. marker) THEN
        (* marker changed, the markers of all using instructions must be 
           recalculated *)
        instr. marker := newMarker;
        res := instr;
        WHILE (res # NIL) DO
          (* add all using instruction to worklist that are part of the current
             loop and whose marker hasn't reached bottom (i.e. `other') yet *)
          use := res. useList;
          WHILE (use # NIL) DO
            IF MarkedInstr (use. instr) & (use. instr. marker # other) THEN
              worklist. AddTail (use. instr)
            END;
            use := use. nextUse
          END;
          res := res. nextResult
        END
      END
    END
  END AnalyseLoop;



PROCEDURE Region (region: D.Region);
  VAR
    r: D.Region;
  
  PROCEDURE MoveInvariantCode (loop, region: D.Region);
  (* Moves loop invariant instructions from `region' into the enclosing region.
     of `loop'.  *)
    VAR
      instr, next: D.Instruction;
    BEGIN
      IF (region = loop) OR (region. opcode # Opc.mergeLoop) THEN
        instr := region. instrList;
        WHILE (instr # NIL) DO
          next := instr. nextInstr;
          IF (instr IS D.Region) THEN
            MoveInvariantCode (loop, instr(D.Region))
          ELSIF (instr. marker = loopInvariant) THEN
            IF (instr. opcode = Opc.gate) THEN
              (* special case: pathological loop gates whose backedge argument
                 is the gate itself *)
              instr. ReplaceUses (instr. opndList. arg)
            ELSE
              loop. region. MoveInstruction (instr)
            END
          END;
          instr := next
        END
      END
    END MoveInvariantCode;
  
  BEGIN
    (* bottom up analysis: first transform nested loops *)
    r := region. regionList;
    WHILE (r # NIL) DO
      r. marker := other;
      Region (r);
      r := r. nextRegion
    END;
    
    IF (region. opcode = Opc.mergeLoop) THEN
      AnalyseLoop (region);
      MoveInvariantCode (region, region)
    END
  END Region;

PROCEDURE GlobalRegion* (greg: D.Region);
  BEGIN
    greg. ClearInfo (loopInvariant);
    greg(D.GlobalRegion). NumberDominanceTree();
    Region (greg)
  END GlobalRegion;

END LoopTransformation.
