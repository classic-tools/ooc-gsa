(*	$Id: GuardCond.Mod,v 2.19 1999/03/19 20:38:53 acken Exp $	*)
MODULE GuardCond;
(*  Calculates control flow relationships between regions.
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
This module inspects all possible paths of control through a global region.  It
calculates a binary relation between all regions of the greg:

If for every path evaluation of region A means that region B is evaluated, too,
then it is said that "A implies B".  Example: every (reachable) region implies
its own execution, and every region implies execution of the topmost region, 
greg.

If for every path evaluation of region A means that region B is not evaluated,
then it is said that "A contradicts B".  Example: two regions appearing as 
argument of a (non-loop) merge (e.g. the two paths through an IF statement) 
contradict each other.  "Contradicts" is symmetric, unlike "implies".

Loops are generally ignored.  They are treated as if they are evaluated just 
once.  The second argument of loop gates is ignored.


The information provided by this module is used in a number of algorithms.  The
optimizers GateReduction and GuardPropagation simplify the GSA code based on
the properties derived here.  The scheduler uses it to avoid introducing 
dependencies between independent (contradicting) paths through a greg when
resolving anti-dependencies.
*)

IMPORT
  D := Data, Opc := Opcode, Sym := SymbolTable;
  

TYPE
  Condition* = RECORD
    value*: D.Usable;  (* boolean value *)
    negate*: BOOLEAN;  (* toggles between `value' and `~value' *)
  END;
  
  RegionInfo* = POINTER TO RegionInfoDesc;
  InfoArray* = POINTER TO ARRAY OF RegionInfo;
  RegionMatrix* = POINTER TO ARRAY OF ARRAY OF SHORTINT;
  RegionSummary* = POINTER TO RegionSummaryDesc;
  RegionSummaryDesc* = RECORD
    infos-: InfoArray;
    matrix-: RegionMatrix;
    count-: INTEGER
  END;
  
  RegionInfoDesc* = RECORD
    (D.InfoDesc)
    region-: D.Region;
    (* the guard this info block belongs to *)
    guard*: Condition;
    (* guard of this region; holds for the range of the region *)
    prefix-: RegionInfo;
    (* reference to region info of enclosing region; all conditions that hold
       for the enclosing region also hold for this one *)
    id-: INTEGER;
    (* index in `RegionSummary' table *)
    summary-: RegionSummary
    (* pointer to info list, region matrix, and region counter *)
  END;
  
CONST
  (* symblic values for `RegionMatrix[i, j]': *)
  unknown* = 0;
  false* = 1;
  true* = 2;
  partialImplication* = 3;               (* `i' implies guard of `j' *)
  implies* = true;                       (* `i' implies execution of `j' *)
  contradicts* = false;                  (* only one of `i'/'j' is executed *)
  
CONST
  fastTrace = TRUE;


PROCEDURE Implies* (VAR c1, c2: Condition): SHORTINT;
(* Returns `true' if "`c1' holds" guarantees that `c2' to hold, `false' if 
   "`c1' holds" implies that `~c2' holds, and `unknown' otherwise.  *)
  BEGIN
    IF (c1. value = c2. value) THEN
      IF (c1. negate = c2. negate) THEN
        RETURN true
      ELSE
        RETURN false
      END
    ELSE
      RETURN unknown
    END
  END Implies;
  
PROCEDURE Unreachable* (r: D.Region): BOOLEAN;
(* Returns TRUE if region `r' is never executed because it is guarded by a
   predicate that never evaluates to TRUE.  *)
  VAR
    ri: RegionInfo;
  BEGIN
    ri := r. info(RegionInfo);
    RETURN (ri. summary. matrix[ri. id, ri. id] = contradicts)
  END Unreachable;

PROCEDURE Contradicting* (ri1, ri2: RegionInfo): BOOLEAN;
(* Returns TRUE if the sequential flow of control passes either through `ri1' 
   or through `ri2' but never but never through both of them.  This is 
   equivalent to `ri1' and `ri2' having contradicting guards.  *)
  BEGIN
    RETURN (ri1. summary. matrix[ri1. id, ri2. id] = contradicts)
  END Contradicting;

PROCEDURE Implication* (ri1, ri2: RegionInfo): BOOLEAN;
(* Returns TRUE if execution of region `ri1' implies that `ri2' is also 
   executed.  Note that nothing is said about the order in which the two 
   are evaluated.  *)
  BEGIN
    RETURN (ri1. summary. matrix[ri1. id, ri2. id] = implies)
  END Implication;



PROCEDURE TraceValue* (startValue: D.Usable; VAR value: D.Usable; 
                       fast: BOOLEAN): BOOLEAN;
(* Reduce `startvalue' to a canonical form.  The final `value' isn't
   a copy or negation instruction, nor the constant FALSE, nor an if-  or cond-
   gate with two constant operands.  The function result is the negation flag:
   `TRUE' means that `startValue' redruces to `~value', otherwise to `value'.
   `fast=TRUE' means that the `info' and `marker' fields of results can be used
   to speed up search.  Note that the `info' field has to be set to NIL 
   initially.  *)
  VAR
    opcode: INTEGER;
    instr: D.Instruction;
    first, second: D.Usable;
    negate, exit, negateFirst, negateSecond: BOOLEAN;
    merge: D.Merge;
    guard: D.Guard;
  BEGIN
    IF fast & (startValue IS D.Result) & (startValue. info # NIL) THEN
      value := startValue. info(D.Usable);
      RETURN (startValue. marker = 1)
    ELSE
      value := startValue;
      negate := FALSE;
      REPEAT
        exit := TRUE;
        IF (value IS D.Instruction) THEN
          instr := value(D.Instruction);
          opcode := instr. opcode;
          
          IF (opcode = Opc.copy) THEN
            value := instr. opndList. arg;
            exit := FALSE
            
          ELSIF (opcode = Opc.notsu) THEN
            value := instr. opndList. arg;
            negate := ~negate;
            exit := FALSE
            
          ELSIF (opcode = Opc.gate) & 
                (instr. opndList. arg(D.Merge). opcode = Opc.mergeLoop) THEN
            (* exit loop *)
            
          ELSIF (opcode = Opc.gate) THEN
            (* check if both operands of the gate are constant *)
            merge := instr. opndList. arg(D.Merge);
            IF (merge. opcode = Opc.mergeIf) OR 
               (merge. opcode = Opc.mergeCond) THEN
              negateFirst := TraceValue (instr. opndList. nextOpnd. arg, first, fast);
              negateSecond := TraceValue (instr. opndList. nextOpnd. nextOpnd. arg, second, fast);
              IF (first = Sym.constTrue) & (second = Sym.constTrue) THEN
                IF (negateFirst = negateSecond) THEN  (* same operands *)
                  value := first; 
                  negate := (negate # negateFirst);
                  exit := FALSE
                ELSIF (merge. opndList. arg IS D.Guard) &
                  (merge. opndList. nextOpnd. arg IS D.Guard) THEN
                  (* the ELSIF guard could be a single boolean expression, but
                     it is to complex for Oberon-A... *)
                  IF (merge. opndList. arg(D.Guard). opndList. arg =
                       merge. opndList. nextOpnd. arg(D.Guard). opndList. arg) THEN
                    (* complementary operands *)
                    guard := merge. opndList. arg(D.Guard);
                    value := guard. opndList. arg;
                    negate := negate # (negateFirst # 
                                        (guard. opcode = Opc.guardFalse));
                    exit := FALSE
                  END
                END
              END
            END
          END
        END
      UNTIL exit;
      
      (* canonicalize boolean constant to `TRUE' plus `negate' flag *)
      IF (value = Sym.constFalse) THEN
        value := Sym.constTrue;
        negate := ~negate
      END;
      
      (* store `value' and `negate' in the result we began with *)
      IF fast & (startValue IS D.Result) THEN
        startValue. info := value;
        IF negate THEN
          startValue. marker := 1
        ELSE
          startValue. marker := 0
        END
      END;
      RETURN negate
    END
  END TraceValue;

PROCEDURE OperandInfo* (opnd: D.Opnd): RegionInfo;
(* Returns the conditions that are known to hold whenever this operand is used
   or visible (in the case of gate operands).  *)
  VAR
    region, arg: D.Opnd;
  BEGIN
    IF (opnd. instr. opcode = Opc.gate) THEN
      region := opnd. instr. opndList. arg(D.Merge). opndList;
      arg := opnd. instr. opndList. nextOpnd;
      WHILE (arg # opnd) DO
        region := region. nextOpnd;
        arg := arg. nextOpnd
      END;
      RETURN region. arg(D.Region). info(RegionInfo)
    ELSE
      RETURN opnd. instr. region. info(RegionInfo)
    END
  END OperandInfo;


PROCEDURE MarkUnreachable (m: RegionMatrix; count: INTEGER; j: INTEGER);
  VAR
    i: INTEGER;
  BEGIN
    FOR i := 0 TO count-1 DO
      m[j, i] := contradicts;
      m[i, j] := contradicts
    END
  END MarkUnreachable;

PROCEDURE InitRegions (region: D.Region; VAR id: INTEGER; summary: RegionSummary);
(* Initializes region info of all regions in `region'.  *)
    
  PROCEDURE CreateRegionInfo (region: D.Region): RegionInfo;
    VAR
      regionInfo, prefix: RegionInfo;

    PROCEDURE Prefix (ri: RegionInfo; value: D.Usable; negate: BOOLEAN): BOOLEAN;
    (* Returns TRUE if `value' holds in `ri' or in one of the regions `ri' is 
       nested in.  *)
      VAR
        c: Condition;
      BEGIN
        c. value := value;
        c. negate := negate;
        WHILE (ri # NIL) DO
          IF (Implies (ri. guard, c) = true) THEN
            RETURN TRUE
          END;
          ri := ri. prefix
        END;
        RETURN FALSE
      END Prefix;
    
    BEGIN
      NEW (regionInfo);
      regionInfo. id := id;
      regionInfo. region := region;
      summary. infos[id] := regionInfo;
      regionInfo. summary := summary;
      INC (id);
      WITH region: D.Guard DO
        CASE region. opcode OF
        | Opc.guardTrue: 
          regionInfo. guard. negate := 
            TraceValue(region. opndList. arg, regionInfo. guard. value, fastTrace)
        | Opc.guardFalse:
          regionInfo. guard. negate := 
            ~TraceValue(region. opndList. arg, regionInfo. guard. value, fastTrace)
        | Opc.guardGreg:
          regionInfo. guard. value := Sym.constTrue;
          regionInfo. guard. negate := FALSE
        | Opc.guardCase: 
          regionInfo. guard. value := region;
          regionInfo. guard. negate := FALSE
        END;
        IF (region. opcode = Opc.guardGreg) THEN
          regionInfo. prefix := NIL
        ELSE
          regionInfo. prefix := region. region. info(RegionInfo);
          (* check if region is unreachable; an unreachable region contradicts 
             all other regions *)
          prefix := regionInfo. prefix;
          IF (summary. matrix[prefix. id, prefix. id] = contradicts) OR
             Prefix (regionInfo, regionInfo. guard. value, 
                     ~regionInfo. guard. negate) THEN
            MarkUnreachable (summary. matrix, summary. count, regionInfo. id)
          END
        END
      | region: D.Merge DO
        (* a merge adds no guards on its own; use the list of the enclosing
           region *)
        regionInfo. guard. value := Sym.constTrue;
        regionInfo. guard. negate := FALSE;
        regionInfo. prefix := region. region. info(RegionInfo)
      END;
      RETURN regionInfo
    END CreateRegionInfo;
  
  BEGIN
    region. info := CreateRegionInfo (region);
    region. marker := 0;
    region := region. regionList;
    WHILE (region # NIL) DO
      InitRegions (region, id, summary);
      region := region. nextRegion
    END
  END InitRegions;

PROCEDURE TransitiveHull (m: RegionMatrix; r: InfoArray; count: INTEGER);
  VAR
    i, j, k: INTEGER;
  
(*  PROCEDURE WM(i0, j0: INTEGER; d: BOOLEAN);
  (* debug; pre: WriteGSA.SetMarkersPos has been run *)
    VAR
      i, j: INTEGER;
    BEGIN
      IF (i0 >= 0) THEN
        Out.String ("("); Out.LongInt (r[i0].region.pos, 0); 
        Out.String (","); Out.LongInt (r[j0].region.pos, 0);
        Out.Char (")");
        IF d THEN
          Out.String ("   ("); Out.LongInt (r[j0].region.pos, 0); Out.String (","); 
          Out.LongInt (r[i0].region.pos, 0); Out.Char (")");
        END;
        Out.Ln;
      END;
      Out.String ("     ");
      FOR i := 0 TO count-1 DO
        Out.String (" ");
        Out.LongInt (r[i].region.pos, 2);
      END;
      Out.Ln;
      FOR i := 0 TO count-1 DO
        Out.LongInt (r[i].region.pos, 2);
        Out.String (":  ");
        FOR j := 0 TO count-1 DO
          Out.String ("  ");
          CASE m[i, j] OF
          | implies: Out.Char ("i")
          | partialImplication: Out.Char ("p")
          | contradicts: Out.Char ("c")
          ELSE
            Out.Char ("-")
          END
        END;
        Out.Ln
      END;
      Out.Ln
    END WM;*)
  
  BEGIN
    FOR i := 0 TO count-1 DO
      FOR j := 0 TO count-1 DO
        IF (m[j, i] = partialImplication) & 
           (m[j, r[i]. prefix. id] = implies) THEN
          m[j, i] := implies
        END;
        IF (m[j, i] = implies) THEN
          FOR k := 0 TO count-1 DO
            CASE m[i, k] OF
            | unknown:  (* ignore *)
            | contradicts:
              m[j, k] := contradicts;
              m[k, j] := contradicts
            | implies:
              IF (m[j, k] # contradicts) THEN
              (* note: if `m[j, k] # contradicts', then region `j' is actually
                 unreachable; I'm not sure if we need to mark `j' as such and
                 restart `TransitiveHull' again from the beginning  --mva *)
                m[j, k] := implies
              END
            | partialImplication:
              IF (m[j, k] = unknown) THEN
                m[j, k] := partialImplication
              END
            END
          END
        END
      END
    END
  END TransitiveHull;

PROCEDURE Init* (greg: D.GlobalRegion);
(* Determines implication and contradiction relationships between regions.  A 
   region A implies region B if, every time A is evaluated, B will be (or has 
   been) evaluated.  A contradicts B if evaluation of A prevents B from being
   evaluated and vice versa.  
   Note that this procedure uses the `info' fields of regions to store 
   information.  These fields cannot be used for another purpose.  `TraceValue'
   makes use of both `info' and `marker' entries of results.  *)
  VAR
    summary: RegionSummary;
    count, i, j, k: INTEGER;
    ri, rj: RegionInfo;
    m: RegionMatrix;
    gateOpnd, opnd, opnd2: D.Opnd;
    negateOpnd: BOOLEAN;
    opndValue: D.Usable;
    merge: D.Merge;
    r0, r1: D.Region;
    
  PROCEDURE CountRegions (r: D.Region): INTEGER;
  (* Counts the number of guards in `r'.  This equivalent to the total number
     of regions minus the merge regions.  *)
    VAR
      sum: INTEGER;
    BEGIN
      sum := 1;
      r := r. regionList;
      WHILE (r # NIL) DO
        INC (sum, CountRegions (r));
        r := r. nextRegion
      END;
      RETURN sum
    END CountRegions;
  
  PROCEDURE AddImplications (info: RegionInfo);
  (* Add (partial) implication entries `info' --> x for all guards x whose 
     predicate holds when the guard of `info' holds.  Analogous reasoning
     introduces contradiction entries.  *)
    VAR
      merge: D.Merge;
      i, j, opn: INTEGER;
      use: D.Opnd;
      opndCond: Condition;
      
    PROCEDURE Implications (i: INTEGER; cond: Condition);
    (* pre: ~(cond. value IS D.Const) *)
      VAR
        use: D.Opnd;
        instr: D.Instruction;
        cond2: Condition;
        opndInfo: RegionInfo;
        j: INTEGER;
      BEGIN
        use := cond. value. useList;
        WHILE (use # NIL) DO
          instr := use. instr;
          CASE instr. opcode OF
          | Opc.copy:
            cond2. value := instr; cond2. negate := cond. negate;
            Implications (i, cond2)
          | Opc.notsu:
            cond2. value := instr; cond2. negate := ~cond. negate;
            Implications (i, cond2)
          | Opc.gate:
            IF (instr. opndList. arg(D.Merge). opcode # Opc.mergeLoop) THEN
              opndInfo := OperandInfo (use);
              IF (m[i, opndInfo. id] = implies) THEN
                cond2. value := instr; cond2. negate := cond. negate;
                Implications (i, cond2)
              END
            END
          | Opc.guardTrue, Opc.guardFalse:
            j := instr. info(RegionInfo). id;
            IF ((instr. opcode = Opc.guardTrue) = cond. negate) THEN
              (* `i' contradicts `j' *)
              m[i, j] := contradicts; m[j, i] := contradicts
            ELSE
              (* `i' (partially) implies `j' *)
              IF (m[i, j] = unknown) THEN
                m[i, j] := partialImplication
              END
            END
          ELSE  (* ignore *)
          END;
          use := use. nextUse
        END
      END Implications;
    
    BEGIN
      i := info. id;
      IF (info. region. opcode = Opc.guardTrue) OR
         (info. region. opcode = Opc. guardFalse) THEN
        IF (info. guard. value = Sym.constTrue) THEN
          IF ~info. guard. negate THEN
            (* regions that are always executed are partially implied by all 
               other regions *)
            FOR j := 0 TO count-1 DO
              IF (m[j, i] = unknown) THEN
                m[j, i] := partialImplication
              END
            END
          END
        ELSE
          opndCond. value := info. region. opndList. arg;
          opndCond. negate := (info. region. opcode = Opc.guardFalse);
          Implications (i, opndCond);
          Implications (i, info. guard)
        END
      END;

      merge := info. region. RegionMerge();
      IF (merge # NIL) & (merge. opcode # Opc.mergeLoop) THEN
        opn := merge. ArgumentIndex (info. region)+1;
        
        (* scan through gates associated with `merge' *)
        use := merge. useList;
        WHILE (use # NIL) DO
          IF (use. instr IS D.Gate) THEN
            (* get operand value; if it's constant, then add partial
               implications for all uses of the gate *)
            opnd := use. instr. NthOperand (opn);
            opndCond. negate := TraceValue (opnd.arg, opndCond.value, fastTrace);
            IF (opndCond. value = Sym.constTrue) THEN
              opndCond. value := use. instr;
              Implications (i, opndCond)
            END
          END;
          use := use. nextUse
        END
      END
    END AddImplications;
  
  PROCEDURE PropagateGuards (r: D.Region);
  (* For every boolean guard in `r' replace all occurences of its argument in
     regions dominated by `r' by the appropriate boolean constant.  *)
    VAR
      use, next: D.Opnd;
    BEGIN
      IF ((r. opcode = Opc.guardTrue) OR (r. opcode = Opc.guardFalse)) &
         ~(r. opndList. arg IS D.Const) THEN
        use := r. opndList. arg. useList;
        WHILE (use # NIL) DO
          next := use. nextUse;
          IF (use. instr # r) & r. Dominates (use. instr. region) &
             use. ValueOperand() THEN
            IF (r. opcode = Opc.guardTrue) THEN
              use. ReplaceOperand (Sym.constTrue)
            ELSE
              use. ReplaceOperand (Sym.constFalse)
            END
          END;
          use := next
        END
      END;
      
      r := r. regionList;
      WHILE (r # NIL) DO
        PropagateGuards (r);
        r := r. nextRegion
      END
    END PropagateGuards;
  
  PROCEDURE InstrDepImplications (r: D.Region);
    VAR
      instr, dep: D.Instruction;
      m: RegionMatrix;
      rIndex, depIndex: INTEGER;
    BEGIN
      rIndex := r. info(RegionInfo). id;
      m := r. info(RegionInfo). summary. matrix;
      instr := r. instrList;
      WHILE (instr # NIL) DO
        WITH instr: D.Region DO
          InstrDepImplications (instr)
        ELSE
          IF (instr. opcode # Opc.gate) THEN
            (* this does not work for gates; agreed, this should not be done
               for the third operand of a loop gate, but I do not know why
               it should not work for all other gates *)
            opnd := instr. opndList;
            WHILE (opnd # NIL) DO
              IF (opnd. arg IS D.Result) THEN
                dep := opnd. arg(D.Result). instr;
                depIndex := dep. region. info(RegionInfo). id;
                IF (m[rIndex, depIndex] # contradicts) THEN
                  m[rIndex, depIndex] := implies
                END
              END;
              opnd := opnd. nextOpnd
            END
          END
        END;
        instr := instr. nextInstr
      END
    END InstrDepImplications;
  
  BEGIN
    greg. NumberDominanceTree();
    PropagateGuards (greg);
    
    (* create region list and region matrix *)
    count := CountRegions (greg);
    NEW (summary);
    NEW (summary. infos, count);
    NEW (m, count, count);
    FOR i := 0 TO count-1 DO
      FOR j := 0 TO count-1 DO
        m[i, j] := unknown
      END
    END;
    summary. matrix := m;
    summary. count := count;

    (* create region info blocks, assign ids to regions *)
    greg. ClearInfo (0);
    count := 0;
    InitRegions (greg, count, summary);
    (* here holds: if `r0' dominates `r1', then 
                   `r0. info. id < r1. info. id' *)
                   
    (* an instruction implies the execution of all regions from which it
       takes arguments *)
    InstrDepImplications (greg);
    
    FOR i := 0 TO count-1 DO
      IF (m[i, i] # contradicts) THEN
        ri := summary. infos[i];
        
        (* region `i' implies itself and the regions it is nested in *)
        WHILE (ri # NIL) DO
          m[i, ri. id] := implies;
          ri := ri. prefix
        END;
        ri := summary. infos[i];

        IF (ri. region IS D.Merge) THEN
          (* the operands of a merge imply execution of the merge *)
          opnd := ri. region. opndList;
          WHILE (opnd # NIL) DO
            rj := ri;
            LOOP
              m[opnd. arg. info(RegionInfo). id, rj. id] := implies;
              merge := rj. region. RegionMerge();
              IF (merge = NIL) OR (merge. opcode = Opc.mergeLoop) THEN
                EXIT
              END;
              rj := merge. info(RegionInfo)
            END;

            IF (ri. region. opcode # Opc.mergeLoop) THEN
              (* the operands of a "merge-if:", "merge-cond:", or "merge-case:"
                 contradict each other *)
              j := opnd. arg. info(RegionInfo). id;
              opnd2 := ri. region. opndList;
              WHILE (opnd2 # NIL) DO
                IF (opnd2 # opnd) THEN
                  k := opnd2. arg. info(RegionInfo). id;
                  m[j, k] := contradicts;
                  m[k, j] := contradicts
                END;
                opnd2 := opnd2. nextOpnd
              END
            END;
            opnd := opnd. nextOpnd
          END
        END;

        (* if the region guard can be traced to a gate with constant operands
           of the `wrong' value, then `ri' implies the other operand's region;
           ignore loop gates, otherwise we might end up with very ugly logical
           conflicts *)
        IF (ri. guard. value IS D.Gate) &
           (ri. guard. value(D.Gate). opndList. arg(D.Merge). opcode #
              Opc.mergeLoop) THEN
          k := 0;
          gateOpnd := ri. guard. value(D.Gate). opndList. nextOpnd;
          WHILE (k <= 1) & (gateOpnd # NIL) DO
            negateOpnd := TraceValue (gateOpnd. arg, opndValue, fastTrace);
            IF (opndValue#Sym.constTrue) OR (negateOpnd=ri. guard. negate) THEN
              opnd2 := gateOpnd;
              INC (k)
            END;
            gateOpnd := gateOpnd. nextOpnd
          END;
          IF (k = 1) THEN
            rj := OperandInfo (opnd2);
            m[i, rj. id] := implies
          END
        END
      END
    END;

    (* a region containing two contradicting guards G1 and G1 implies all 
       regions that are implied by both G1 and G2 *)
    FOR i := count-1 TO 0 BY -1 DO
      r0 := summary. infos[i]. region. regionList;
      WHILE (r0 # NIL) DO
        r1 := r0. nextRegion;
        WHILE (r1 # NIL) DO
          IF (r0 IS D.Guard) & (r1 IS D.Guard) &
             (m[r0. info(RegionInfo). id, r0. info(RegionInfo). id] #
               contradicts) &
             (m[r1. info(RegionInfo). id, r1. info(RegionInfo). id] #
               contradicts) &
             Contradicting (r0. info(RegionInfo), r1. info(RegionInfo)) THEN
            FOR j := 0 TO count-1 DO
              IF (m[r0. info(RegionInfo). id, j] = implies) &
                 (m[r1. info(RegionInfo). id, j] = implies) THEN
                m[i, j] := implies
              END
            END
          END;
          r1 := r1. nextRegion
        END;
        r0 := r0. nextRegion
      END
    END;

    (* add partial implication and contradiction entries to `m' *)
    FOR i := 1 TO count-1 DO
      ri := summary. infos[i];
      IF ~(ri. region IS D.Merge) OR (ri. region. RegionMerge() # NIL) THEN
        AddImplications (ri)
      END
    END;
    
    TransitiveHull (m, summary. infos, count)
  END Init;

PROCEDURE RemoveDeadReferences* (greg: D.GlobalRegion);
(* Brings the region implication/contradiction information up to date after a
   dead code elimination.  This way a costly (second) run of `Init' can be 
   avoided.  *)
  VAR
    s: RegionSummary;
    start, i, j, delta, d: INTEGER;
  
  PROCEDURE Dead (i: INTEGER): BOOLEAN;
    BEGIN
      RETURN (s. infos[i]. region. region = NIL)
    END Dead;
  
  BEGIN
    s := greg. info(RegionInfo). summary;
    start := 1;
    WHILE (start # s. count) & ~Dead (start) DO
      INC (start)
    END;

    (* remove dead rows of summary matrix *)
    delta := 0;
    FOR i := start TO s. count-1 DO
      IF Dead (i) THEN
        DEC (delta)
      ELSE
        FOR j := 0 TO s. count-1 DO
          s. matrix[i+delta, j] := s. matrix[i, j]
        END
      END
    END;
    d := delta;
    
    (* remove dead columns of matrix, clean up conditions *)
    delta := 0;
    FOR j := start TO s. count-1 DO
      IF Dead (j) THEN
        DEC (delta)
      ELSE
        FOR i := 0 TO s. count-1+d DO
          s. matrix[i, j+delta] := s. matrix[i, j]
        END
      END
    END;

    (* remove dead elements of array *)
    delta := 0;
    FOR i := start TO s. count-1 DO
      IF Dead (i) THEN
        DEC (delta)
      ELSE
        INC (s. infos[i]. id, delta);
        s. infos[i+delta] := s. infos[i]
      END
    END;
    INC (s. count, delta)
  END RemoveDeadReferences;

END GuardCond.
