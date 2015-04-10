(*	$Id: ControlFlow.Mod,v 1.4 1999/03/19 20:39:45 acken Exp $	*)
MODULE ControlFlow;
(*  Transforms GSA code into a linear sequence of instructions.
    Copyright (C) 1996, 1999  Michael van Acken

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
  D := Data, Opc := Opcode, Class := Classify, Allocate;
  
  
CONST  (* pseudo instructions inserted by this module *)
  jump* = Opc.maxOpcode+1;
  (* "jump <target>"
     Unconditional jump to instruction <target>.  Last instruction in every
     region (except greg).  *)

  branchOnFalse* = jump+2;
  (* "branch-on-false <target>"
     Branch jump to instruction <target> if its guard fails.  Always first 
     instruction of the guard; not present in the global region.  *)

  branchOnTrue* = jump+3;
  (* "branch-on-true <target>"
     Branch jump to instruction <target> if its guard succeeds.  Always first 
     instruction of the guard; not present in the global region.  *)

  assignGates* = jump+4;
  (* "assign-gates <merge>"
     Marks the place where assignments corresponding to gates have to be 
     placed.  The set of gates in question belongs to region <merge>, and the
     gate operand is designated by the current region.  *)

  endOfGreg* = jump+5;
  (* "end-of-greg"
     A no-operation instruction placed at the end of the global region.  Can
     serve as target of a jump or branch.  *)
  

PROCEDURE CreateInstr (region: D.Region; opcode: INTEGER; 
                       atBeginning: BOOLEAN): D.Instruction;
  VAR
    instr: D.Instruction;
  BEGIN
    instr := region. CreateInstruction (opcode, D.struct[D.strUndef], D.undefPos);
    instr. marker := 0;
    INCL (instr. flags, Class.instrVoid);
    IF atBeginning THEN
      instr. MoveBehind (NIL)
    ELSE
      instr. MoveInFront (NIL)
    END;
    RETURN instr
  END CreateInstr;

PROCEDURE SetTarget (instr, target: D.Instruction);
  BEGIN
    IF (instr. opndList # NIL) THEN
      DEC (instr. opndList. arg(D.Instruction). marker);
      instr. opndList. ReplaceOperand (target)
    ELSE
      instr. Operand (target)
    END;
    INC (target. marker)
  END SetTarget;

PROCEDURE DisableInstr (instr: D.Instruction);
  VAR
    opc: INTEGER;
  BEGIN
    IF ~(Class.instrNoOutput IN instr. flags) THEN
      opc := instr. opcode;
      IF (opc = jump) OR (opc = branchOnTrue) OR (opc = branchOnFalse) THEN
        DEC (instr. opndList. arg(D.Instruction). marker)
      END;
      INCL (instr. flags, Class.instrNoOutput)
    END
  END DisableInstr;

PROCEDURE NoOutput (instr: D.Instruction): BOOLEAN;
  BEGIN
    RETURN (Class.instrNoOutput IN instr. flags) &
             ((instr. opcode # Opc.accessHeap) &
                (instr. opcode # Opc.updateHeap) OR
              ~(D.instrCheckNil IN instr. flags))
  END NoOutput;


PROCEDURE PlaceInstructions (r: D.Region);
(* Places assign-gates at end of regions that have assignments to gate 
   locations and in front of loop merges.  A branch-on-false instruction is
   added to every guard as first instruction, and a jump instruction is 
   appended to the instructions list of every region.  *)
  VAR
    instr, goto: D.Instruction;
    merge: D.Merge;
    
  PROCEDURE AssignsToGates (r,  merge: D.Region): BOOLEAN;
  (* Returns TRUE if `merge' contains gates that make assignments necessary in
     `r'.
     pre: Opc.RegionMerge(r)=merge  *)
    VAR
      use: D.Opnd;
      arg: D.Usable;
      opn: INTEGER;
    BEGIN
      opn := merge. ArgumentIndex (r)+1;
      use := merge. useList;
      WHILE (use # NIL) DO
        IF (use. instr. opcode = Opc.gate) &
           ~(Class.instrVoid IN use. instr. flags) THEN
          arg := use. instr. NthArgument (opn);
          WITH arg: D.Instruction DO
            IF (use. instr. location # NIL) &
               (use. instr. location IS Allocate.Location) &
               (arg. location # NIL) &
               (arg. location IS Allocate.Location) &
               (arg. location(Allocate.Location). value^ #
                  use. instr. location(Allocate.Location). value^) THEN
              RETURN TRUE
            END
          ELSE
            RETURN TRUE
          END
        END;
        use := use. nextUse
      END;
      RETURN FALSE
    END AssignsToGates;
    
  BEGIN
    (* place assign-gates instructions *)
    merge := r. RegionMerge();
    IF (merge # NIL) & AssignsToGates (r, merge) THEN
      instr := CreateInstr (r, assignGates, FALSE);
      instr. Operand (merge)
    END;
    IF (r. opcode = Opc.mergeLoop) & AssignsToGates (r. region, r) THEN
      instr := CreateInstr (r. region, assignGates, FALSE);
      instr. Operand (r);
      instr. MoveInFront (r)
    END;
    
    (* place jump and branch instructions *)
    IF (r. region = NIL) THEN
      instr := CreateInstr (r, endOfGreg, FALSE)
    ELSE
      IF (r IS D.Guard) THEN
        instr := CreateInstr (r, branchOnFalse, TRUE);
      END;
      instr := CreateInstr (r, jump, FALSE);
      
      (* set the jump target for some merge-cond regions; this is easier before
         merges have been moved around *)
      IF (merge = NIL) & (r. opcode = Opc.mergeCond) THEN
        goto := r. nextInstr;
        WHILE (goto IS D.Merge) & (goto. opcode # Opc.mergeLoop) DO
          goto := goto. nextInstr
        END;
        SetTarget (instr, goto)
      END
    END;
    
    r := r. regionList;
    WHILE (r # NIL) DO
      PlaceInstructions (r);
      r := r. nextRegion
    END
  END PlaceInstructions;

PROCEDURE SetTargets (r: D.Region);
(* Adds operands describing the target to jump and branch instructions.  *)
  VAR
    instr, goto: D.Instruction;
    merge: D.Merge;

  PROCEDURE JumpTarget (region: D.Region): D.Instruction;
  (* Returns the next instruction that is executed whenever control leaves the
     given region.
     pre: merges have been moved into the last of their respective entering 
       paths  *)
    VAR
      merge: D.Merge;
    BEGIN
      LOOP
        merge := region. RegionMerge();
        IF (merge # NIL) & (merge. region # region) THEN
          RETURN merge
        ELSIF (region. nextInstr = NIL) THEN
          region := region. region
        ELSE
          RETURN region. nextInstr
        END
      END
    END JumpTarget;  

  PROCEDURE BranchTarget (guard: D.Guard): D.Instruction;
  (* Returns the next instruction that is executed whenever the guard evaluates
     to FALSE.  
     pre: merges have been moved into the last of their entering paths
     post: result # NIL  *)
    VAR
      instr: D.Instruction;

    PROCEDURE ComplementaryGuards (i0, i1: D.Instruction): BOOLEAN;
      BEGIN
        RETURN
          (i0 # NIL) & (i1 # NIL) &
          ((i0. opcode = Opc.guardTrue) & (i1. opcode = Opc.guardFalse) OR
           (i0. opcode = Opc.guardFalse) & (i1. opcode = Opc.guardTrue)) &
          (i0. opndList. arg = i1. opndList. arg)
      END ComplementaryGuards;

    BEGIN
      instr := guard. nextInstr;
      WHILE (instr # NIL) & (instr. nextInstr # NIL) & NoOutput (instr) DO
        instr := instr. nextInstr
      END;
      IF (instr = NIL) THEN
        instr := JumpTarget (guard. region)
      END;
      IF ComplementaryGuards (guard, instr) THEN
        instr := instr(D.Region). instrList. nextInstr (* skip branch *)
      END;
      RETURN instr
    END BranchTarget;

  BEGIN
    IF (r IS D.Guard) & (r. region # NIL) THEN
      SetTarget (r. instrList, BranchTarget (r(D.Guard)))
    END;
    
    IF (r. region # NIL) THEN
      instr := r. instrTail;
      IF (instr. opndList = NIL) THEN
        merge := r. RegionMerge();
        IF (merge # NIL) & (merge. opcode = Opc.mergeLoop) THEN
          goto := merge
        ELSE
          goto := JumpTarget (r)
        END;
        SetTarget (instr, goto)
      END
    END;
    
    r := r. regionList;
    WHILE (r # NIL) DO
      SetTargets (r);
      r := r. nextRegion
    END
  END SetTargets;

PROCEDURE InitRegionMarkers (r: D.Region);
(* Sets the `marker' field of every merge in `r' to -(#operands).  *)
  BEGIN
    IF (r IS D.Merge) & (r. opcode # Opc.mergeLoop) THEN
      r. marker := -r. NumOfOperands()
    END;
    r := r. regionList;
    WHILE (r # NIL) DO
      InitRegionMarkers (r);
      r := r. nextRegion
    END
  END InitRegionMarkers;

PROCEDURE MoveMerges (r: D.Region; force: BOOLEAN);
(* Moves all (non-loop) merges into the region corresponding to the last 
   (i.e. placed farthest down in the C code) path into the merge.  The merge
   will be the next to last instruction in this region (the last is a jump).
   pre: InitRegionMarkers has been run beforehand.  *)
  VAR
    merge: D.Merge;
    instr: D.Instruction;
  BEGIN
    IF force OR ~(r IS D.Merge) OR (r. opcode = Opc.mergeLoop) THEN
      (* if `r' continues into a merge, and `r' is the last region of the 
         merge, then pull `merge' into the output of `r'  *)
      merge := r. RegionMerge();
      IF (merge # NIL) & (merge. opcode # Opc.mergeLoop) THEN
        INC (merge. marker);
        IF (merge. marker = 0) THEN
          instr := r. instrTail;
          r. MoveInstruction (merge);
          (* move merge in front of the region's final jump instruction *)
          merge. MoveInFront (instr);
          MoveMerges (merge, TRUE)
        END
      END;

      (* note: while `r. instrList' corresponds to the sequence of 
         instructions emitted by the scheduler, `r. regionList' isn't sorted
         in any way *)
      instr := r. instrList;
      WHILE (instr # NIL) DO
        IF (instr IS D.Region) THEN
          MoveMerges (instr(D.Region), FALSE)
        END;
        instr := instr. nextInstr
      END
    END
  END MoveMerges;

PROCEDURE NextInstr (instr: D.Instruction): D.Instruction;
(* Get instruction following `instr' in the emitted code.  *)
  BEGIN
    REPEAT
      IF (instr IS D.Region) THEN
        instr := instr(D.Region). instrList
      ELSE
        WHILE (instr. nextInstr = NIL) DO
          instr := instr. region
        END;
        instr := instr. nextInstr
      END
    UNTIL ~(NoOutput (instr) OR (instr IS D.Region));
    RETURN instr
  END NextInstr;

PROCEDURE JumpChaining (r: D.Region);
(* Make jumps point to instruction that do translate to C.  Perform jump 
   chaining: jumps to jumps are pointed to the final target.  
   post: Jumps point to instruction that do translate to C (or assembler), and
   no goto instruction is the target of another goto.  *)
  
  PROCEDURE Chain (instr: D.Instruction);
    VAR
      target: D.Instruction;
    BEGIN
      target := instr. opndList. arg(D.Instruction);
      LOOP
        (* jump chaining: if branching or jumping to a jump, then use the
           second jump's target *)
        WHILE (target. opcode = jump) DO
          target := target. opndList. arg(D.Instruction)
        END;
        IF NoOutput (target) OR (target IS D.Region) THEN
          target := NextInstr (target)
        ELSE
          EXIT
        END
      END;
      IF (target # instr. opndList. arg(D.Instruction)) THEN
        SetTarget (instr, target)
      END
    END Chain;
  
  BEGIN
    IF (r. region # NIL) THEN
      IF (r IS D.Guard) THEN
        Chain (r. instrList)            (* branch *)
      END;
      Chain (r. instrTail)              (* jump *)
    END;
    
    r := r. regionList;
    WHILE (r # NIL) DO
      JumpChaining (r);
      r := r. nextRegion
    END
  END JumpChaining;

PROCEDURE RemoveUnreachable (r: D.Region);
  VAR
    next: D.Instruction;
  BEGIN
    IF (r. region # NIL) & ~(Class.instrNoOutput IN r. instrTail. flags) THEN
      next := NextInstr (r. instrTail);
      WHILE (next. marker = 0) & (next. opcode # endOfGreg) DO
        DisableInstr (next);
        next := NextInstr (next)
      END;
      IF (next = r. instrTail. opndList. arg) THEN
        (* we are jumping to the next instruction: get rid of jump *)
        DisableInstr (r. instrTail)
      END
    END;
    
    r := r. regionList;
    WHILE (r # NIL) DO
      RemoveUnreachable (r);
      r := r. nextRegion
    END
  END RemoveUnreachable;

PROCEDURE OptimizeBranches (r: D.Region);
  VAR
    instr, next, next2: D.Instruction;
  BEGIN
    instr := r. instrList;
    WHILE (instr # NIL) DO
      IF (instr IS D.Region) THEN
        OptimizeBranches (instr(D.Region))
      ELSIF (instr. opcode = branchOnFalse) &
            ~(Class.instrNoOutput IN instr. flags) THEN
        next := NextInstr (instr);
        IF (next. opcode = jump) THEN
          next2 := NextInstr (next);
          IF (next2 = instr. opndList. arg) THEN
            (* branch points to instruction after jump: move jump target
               into branch, remove jump *)
            instr. opcode := branchOnTrue;
            SetTarget (instr, next. opndList. arg(D.Instruction));
            DisableInstr (next)

          ELSIF (next. opndList. arg(D.Instruction). info # NIL) THEN
            (* backwards jump of a loop: move backwards jump into branch *)
            instr. opcode := branchOnTrue;
            next2 := instr. opndList. arg(D.Instruction);
            SetTarget (instr, next. opndList. arg(D.Instruction));
            SetTarget (next, next2)
          END
        END
      END;
      instr. info := instr;  (* mark instruction as visited *)
      instr := instr. nextInstr
    END
  END OptimizeBranches;

PROCEDURE GlobalRegion* (greg: D.GlobalRegion);
(* Adds jump and branch instruction to the GSA code.  Moves merges to their
   places in the emitted code.  The result is a rearranged and extended GSA
   code that can be translated to C (or assembler) in a single, linear pass 
   over the code.  
   Note: Instructions serving as target of a jump or branch are marked with the
   flag `Class.instrJumpTarget' and their `marker' attribute contains a
   unique label id (a non negative number).
   pre: Instruction scheduling and register allocations has been done.  *)
  VAR
    countLabel: LONGINT;
    
  PROCEDURE MarkTargets (r: D.Region);
  (* Sets flag `instrJumpTarget' for all instructions that are the target of
     a jump or branch instruction and assigns an unique id to each one of 
     them.  *)
    VAR
      instr: D.Instruction;
    BEGIN
      instr := r. instrList;
      WHILE (instr # NIL) DO
        IF (instr. marker > 0) THEN
          INCL (instr. flags, Class.instrJumpTarget);
          instr. marker := countLabel;
          INC (countLabel)
        END;
        IF (instr IS D.Region) THEN
          MarkTargets (instr(D.Region))
        END;
        instr := instr. nextInstr
      END
    END MarkTargets;
  
  BEGIN
    greg. ClearInfo (0);
    (* invariant maintained through the rest of this procedure: 
       an instruction's attribute marker holds the number of (active) jumps 
       resp. branches to this instruction *)
    
    (* place jump and branch instructions into the regions; also add
       assign-gates instructions to regions that need them *)
    PlaceInstructions (greg);
    (* move merges to the place they have in the C code *)
    InitRegionMarkers (greg); MoveMerges (greg, FALSE);

    (* set jump and branch targets *)
    SetTargets (greg);
    (* get rid of redundant jumps and branches; remove unreachable 
       instructions *)
    JumpChaining (greg);
    RemoveUnreachable (greg);
    OptimizeBranches (greg);
    RemoveUnreachable (greg);  
    (* ... this is not optimal; RemoveUnreachable may uncover more optimization
       opportunities for OptimizeBranches and vice versa; to get an optimal
       result one would have to implement some kind of sparse control flow
       analysis *)
    
    (* mark all instructions that serve as target of a jump or branch and 
       assign unique ids to them; remove unreachable code behind jumps *)
    countLabel := 0;
    MarkTargets (greg)
  END GlobalRegion;

END ControlFlow.
