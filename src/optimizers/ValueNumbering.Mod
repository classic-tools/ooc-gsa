(* 	$Id: ValueNumbering.Mod,v 2.5 1999/03/15 18:54:17 acken Exp $	 *)
MODULE ValueNumbering;
(*  Value numbering, common subexpression elimination
    Copyright (C) 1996-1999  Juergen Zimmermann

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
  Opc := Opcode, D :=Data, WL := Worklist;

  
TYPE
  Partition = POINTER TO PartitionDesc;
  InstrNode = POINTER TO InstrNodeDesc;
  
  PartitionList = Partition;
  
  
TYPE
  InstrList = POINTER TO InstrListDesc;

TYPE
  InstrListDesc = RECORD
    nextInstrList: InstrList;
    instr: D.Instruction;
  END;

TYPE
  PartitionDesc = RECORD
    nextPartition: Partition; (* next partition in list *)

    splittedBy: Partition; 
      (* The partition which split this one into `subIncl' and `subExcl' 
         at operand position `atOpndPos' into
         those sub-partitions. *)

    atOpndPos: LONGINT; 
      (* Operand position at which splitting by `splitBy' was done *)
      
    super: Partition;
      (* Partition of which this partition is a sub-partition, i.e.
         (self = super. subIncl) OR (self = super. subExcl) holds. *)

    instrNodeList: InstrNode;
      (* instructions within this partition *)
    numOfInstr: LONGINT;

    
    tmpLink: Partition; (* internal worklist link *)
    inWorklist: BOOLEAN; (* TRUE, iff partition is on internal worklist *)
    
    
    usedForSplitting: BOOLEAN; (* did this partition already split others? *)
  END;

  InstrNodeDesc = RECORD(D.InfoDesc);
    nextInstrNode: InstrNode;
    instr: D.Instruction;
    partition: Partition; (* the instruction's partition *)
    
    loopMerge: D.Merge; (* if # NIL, this points to the loop-merge
                           of the most inner loop this instruction is not
                           invariant to *)
  END;


VAR
  partitionList: PartitionList;
  sizeOnePartitions: PartitionList;
    (* this list holds only paritions, which have the size one and which
       have already splitted others. Due to their nature (only one instruction),
       it has no effect, if they are splitted, and because they already splitted
       others. *)
  
  collectPartitions: ARRAY (Opc.maxOpcode + 1) OF Partition;

  
TYPE
  MoveDifferentProc = PROCEDURE (current: Partition; VAR created: PartitionList);

    
PROCEDURE (list: PartitionList) Concatenate (tail: PartitionList);
  VAR
    part: Partition;
  BEGIN
    part := list;
    WHILE (part. nextPartition # NIL) DO
      part := part. nextPartition;
    END;
    part. nextPartition := tail;
  END Concatenate;


PROCEDURE NewInstrNode (instr: D.Instruction): InstrNode;
  VAR
    node: InstrNode;
  BEGIN
    NEW (node);
    node. nextInstrNode := NIL;
    node. instr := instr;
    node. partition := NIL;
    node. loopMerge := NIL;
    RETURN node;    
  END NewInstrNode;


PROCEDURE NewPartition (super: Partition): Partition;
  VAR
    part: Partition;
  BEGIN
    NEW (part);
    part. nextPartition := NIL;
    part. instrNodeList := NIL;
    part. numOfInstr := 0;
    
    part. atOpndPos := -1;
    part. super := super;
    part. splittedBy := NIL;
    
    part. tmpLink := NIL;
    part. inWorklist := FALSE;
    
    part. usedForSplitting := FALSE;
    
    RETURN part;
  END NewPartition;


PROCEDURE (partition: Partition) IncludeInstrNode (instrNode: InstrNode);
  BEGIN
    ASSERT (instrNode. partition = NIL);
    ASSERT (instrNode. nextInstrNode = NIL);
    instrNode. partition := partition;
    instrNode. nextInstrNode := partition. instrNodeList;
    partition. instrNodeList := instrNode;
    INC (partition. numOfInstr);
  END IncludeInstrNode;

PROCEDURE (partition: Partition) ExcludeInstrNode (instrNode: InstrNode);
  VAR
    preInstrNode: InstrNode;
  BEGIN
    ASSERT (instrNode. partition = partition);
    
    IF (instrNode = partition. instrNodeList) THEN
      partition. instrNodeList := instrNode. nextInstrNode;
    ELSE    
      preInstrNode := partition. instrNodeList;
      WHILE (preInstrNode # NIL) & (preInstrNode. nextInstrNode # instrNode) DO
        preInstrNode := preInstrNode. nextInstrNode;
      END;
      ASSERT (preInstrNode # NIL);
      preInstrNode. nextInstrNode := instrNode. nextInstrNode;
    END;
    
    instrNode. nextInstrNode := NIL;
    instrNode. partition := NIL;
    DEC (partition. numOfInstr);
  END ExcludeInstrNode;

PROCEDURE (partition: Partition) Size (): LONGINT;
  BEGIN
    RETURN partition. numOfInstr;
  END Size;

PROCEDURE (partition: Partition) GetAnyInstruction (): InstrNode;
  VAR
    instrNode: InstrNode;
  BEGIN
    instrNode := partition. instrNodeList;
    RETURN instrNode;
  END GetAnyInstruction;

PROCEDURE (partition: Partition) IsEmpty (): BOOLEAN;
  BEGIN
    RETURN (partition.Size () = 0);
  END IsEmpty;


PROCEDURE (partition: Partition) CreateInstrList (): InstrList;
  VAR
    walk: InstrNode;
    instrList, node: InstrList;
  BEGIN
    ASSERT (partition.Size () > 0);
    instrList := NIL;
    walk := partition. instrNodeList;
    WHILE (walk # NIL) DO
      NEW (node);
      node. instr := walk. instr;
      node. nextInstrList := instrList;
      instrList := node;
      walk := walk. nextInstrNode;
    END;
    RETURN instrList;
  END CreateInstrList;


PROCEDURE SameOperandArgument (opnd1, opnd2: D.Opnd): BOOLEAN;
  BEGIN
    RETURN (opnd1. arg = opnd2. arg);
  END SameOperandArgument;

PROCEDURE OwnPartitionAsDefault (instr: D.Instruction): BOOLEAN;
(* TRUE, if `instr' must be moved into a partition on its own,
   i.e. there exist no equalivalen instructions for it. *)
  BEGIN
    RETURN (D.instrUniqueResult IN instr. flags) OR (instr IS D.Region);
  END OwnPartitionAsDefault;

PROCEDURE Available (res: D.Instruction; reg: D.Region): BOOLEAN;
(* TRUE, iff result of instruction `res' is available in region `reg' *)
(* hints for this procedure from MvA ... *)
  BEGIN
    IF (res IS D.Region) THEN
      RETURN FALSE;
    ELSIF ~(res IS D.Gate) THEN
      RETURN res. region. Dominates (reg);
    END;
    RETURN FALSE;
  END Available;


PROCEDURE AddToWorklistUnique (VAR worklist: Partition; part: Partition);
  BEGIN
    IF ~part.inWorklist THEN
      part. tmpLink := worklist;
      part. inWorklist := TRUE;
      worklist := part;
    END;
  END AddToWorklistUnique;

PROCEDURE ClearWorklist (VAR worklist: PartitionList);
  (* unlink worklist *)
  VAR
    walk, next: Partition;
  BEGIN
    walk := worklist;
    WHILE (walk # NIL) DO
      next := walk. tmpLink;
      walk. tmpLink := NIL;
      walk. inWorklist := FALSE;
      walk := next;
    END;
    worklist := NIL;
  END ClearWorklist;

PROCEDURE PartitionInWorklist (part: Partition; worklist: PartitionList): BOOLEAN;
  BEGIN
    RETURN part. inWorklist;
  END PartitionInWorklist;


PROCEDURE Normalize (reg: D.Region);
  VAR
    instr: D.Instruction;
    opnd1, opnd2, opnd3: D.Opnd;
    arg1, arg2: D.Usable;
    class, subClass, newOpcode: INTEGER;
  BEGIN
    instr := reg. instrList;
    WHILE (instr # NIL) DO
      WITH instr: D.Region DO
        Normalize (instr);
      ELSE
        IF (instr. opndList # NIL) & (instr. opndList. nextOpnd # NIL) THEN
          opnd1 := instr. opndList;
          opnd2 := instr. opndList. nextOpnd;
          arg1 := opnd1. arg;
          arg2 := opnd2. arg;

          class := instr. opcode DIV Opc.sizeClass;
          subClass := instr. opcode MOD Opc.sizeClass;
          
          (* strategy:
             - constant value always at second position
             - if there is no constant, put the object at the second position
             - otherwise sort by opcode *)
          IF ((arg1 IS D.Const) & ~(arg2 IS D.Const)) OR
             ((arg1 IS D.Object) & ~(arg2 IS D.Const)) OR
             ((arg1 IS D.Result) & (arg2 IS D.Result) & 
              (arg1(D.Result). instr. opcode > arg2(D.Result). instr. opcode)) THEN
            CASE class OF
            | Opc.classAdd, Opc.classMult,
              Opc.classInter, Opc.classSymDiff, Opc.classUnion,
              Opc.classEql, Opc.classNeq:
              newOpcode := instr. opcode
            | Opc.classLss:
              newOpcode := (Opc.classGtr * Opc.sizeClass) + subClass;
            | Opc.classLeq:
              newOpcode := (Opc.classGeq * Opc.sizeClass) + subClass;
            | Opc.classGtr:
              newOpcode := (Opc.classLss * Opc.sizeClass) + subClass;
            | Opc.classGeq:
              newOpcode := (Opc.classLeq * Opc.sizeClass) + subClass;
            ELSE
              newOpcode := -1;
            END;
            IF (newOpcode >= 0) THEN
              opnd1. SwapArguments (opnd2);
              IF (subClass >= Opc.subclStr) THEN
                (* if comparing strings, also switch the address values *)
                opnd3 := instr. NthOperand (2);
                opnd3. SwapArguments (instr. NthOperand (3));
              END;
              instr. opcode := newOpcode;
            END;
          END;
        END;
      END;
      instr := instr. nextInstr;
    END;
  END Normalize;



PROCEDURE MarkLoopDependentInstr (reg: D.Region);
(* Set `instr. info(InstrNode). loopMerge' field for every loop dependent
   instruction to the corresponding loop-merge. If an instruction `seems'
   to depend on more than one loop, the most inner one is taken.
   An instruction is loop-dependent for loop "L", if it belongs to a region 
   enclosed by "L" and depends on another loop-dependent instruction.
   Loop-Gates of loop "L" are always loop-dependent.
*)

(* pre: Dominance tree is build, see Data.Mod for explanation *)
  VAR
    walk: D.Region;
    worklist: WL.Worklist;
    iInstr: D.Info;
    result: D.Result;
  
  PROCEDURE AddUsingInstrUniqueIn (VAR wl: WL.Worklist; used: D.Result; merge: D.Merge);
    VAR
      use: D.Opnd;
      instr: D.Instruction;
    BEGIN
      use := used. useList;
      WHILE (use # NIL) DO
        instr := use. instr;
        IF merge. Dominates (instr. region) & (instr. info(InstrNode). loopMerge # merge) THEN
          (* instruction was not dependent on current loop-merge, but maybe on an outer one *)
          instr. info(InstrNode). loopMerge := merge;
          wl.AddTailUnique (instr);
        END;
        use := use. nextUse;
      END;
    END AddUsingInstrUniqueIn;
  
  BEGIN
    IF (reg. opcode = Opc.mergeLoop) THEN
      (* only look for loop merges, add all instructions which are dependent on this *)
      worklist.Init;
      AddUsingInstrUniqueIn (worklist, reg, reg(D.Merge));
      WHILE ~worklist.IsEmpty() DO
        (* fetch `instr' from `worklist' *)
        iInstr := worklist. GetHead ();
        worklist.RemoveHead;

        result := iInstr(D.Instruction);
        WHILE (result # NIL) DO
          AddUsingInstrUniqueIn (worklist, result, reg(D.Merge));
          result := result. nextResult;
        END;
      END;
    END;

    (* dig deeper *)
    walk := reg. regionList;   
    WHILE (walk # NIL) DO
      MarkLoopDependentInstr (walk);
      walk := walk. nextRegion;
    END;
  END MarkLoopDependentInstr;


PROCEDURE InitCollectPartitions;
(* sets all elements of array `collectPartitions' to NIL *)
  VAR
    i: LONGINT;
  BEGIN
    FOR i := 0 TO Opc.maxOpcode DO
      collectPartitions[i] := NIL;
    END;
  END InitCollectPartitions;

PROCEDURE ClassifyInstructions (reg: D.Region);
(* Inspects all instructions of region `reg' (and embeded regions)
   and put them into the appropriate worklist of array `collectPartitions' 
   which is determined by the instruction's opcode. If the corresponding 
   array entry (which is the worklist) does not exist, it is created 
   and initialized. *)
  VAR
    instr: D.Instruction;
  
  PROCEDURE IncludeInPartition (instr: D.Instruction);
    BEGIN
      instr. info := NewInstrNode (instr);
      
      IF (collectPartitions[instr. opcode] = NIL) THEN        
        collectPartitions[instr. opcode] := NewPartition (NIL);
      END;
      collectPartitions[instr. opcode]. IncludeInstrNode (instr. info(InstrNode));
    END IncludeInPartition;
    
  BEGIN
    IncludeInPartition (reg);
    instr := reg. instrList;
    WHILE (instr # NIL) DO
      WITH instr: D.Region DO
        ClassifyInstructions (instr);
      ELSE
        IncludeInPartition (instr);
      END;
      instr := instr. nextInstr;
    END;
  END ClassifyInstructions;

PROCEDURE CollectNonEmptyPartitions;
(* move all non-NIL and nonempty elements from array `collectPartitions'
   to the `partitionList' *)
  VAR
    i: LONGINT;
  BEGIN
    partitionList := NIL;
    sizeOnePartitions := NIL;
    FOR i := 0 TO Opc.maxOpcode DO
      IF (collectPartitions[i] # NIL) THEN
        collectPartitions[i]. nextPartition := partitionList;
        partitionList := collectPartitions[i];
      END;
    END;
  END CollectNonEmptyPartitions;


PROCEDURE PartitionByPredicate (mdp: MoveDifferentProc);
  VAR
    current: Partition;
    newParts: PartitionList; 
    createdParts: PartitionList;
  BEGIN
    createdParts := NIL;
    current := partitionList;
    
    WHILE (current # NIL) DO
      newParts := NIL;
      mdp (current, newParts);
      
      IF (newParts # NIL) THEN
        IF (createdParts = NIL) THEN
          createdParts := newParts;
        ELSE
          newParts.Concatenate (createdParts);
          createdParts := newParts;
        END;
      END;

      IF (current. nextPartition = NIL) & (createdParts # NIL) THEN
        (* concatenate partitionList with createdParts *)
        partitionList.Concatenate (createdParts); (* current. nextPartition := createdParts; *)
        createdParts := NIL;
      END;
      
      current := current. nextPartition;
    END;
  END PartitionByPredicate;


PROCEDURE MoveDifferentSignature (current: Partition; VAR created: PartitionList);
(* takes the first instruction within `partition'
   as `pivotInstr' and compares all others instruction of 
   that partition with it in respect to:
   - number of operands (which must be the same)
   - number of results (which must be the same)
   + special instruction like `reclaim', `collect' and `new'
     are moved into one partition for each instruction.      
*)     
  VAR
    instrNode: InstrNode;
    pivotInstr: D.Instruction;
    pivotOperands, pivotResults: INTEGER;
    nextInstrNode: InstrNode;
    moveIt: BOOLEAN;

  PROCEDURE MoveInstrIntoOwnPartition (current: Partition; VAR created: PartitionList);
  (* Move all instructions within `current' into a partition of their own.
     Those newly created partitions are returned in `created' as a partition list.
     One instruction will be left in `current', though *)
     
    VAR
      instrNode: InstrNode;
      newlyCreated: Partition;
    BEGIN
      created := NIL;
      WHILE (current.Size () > 1) DO
        instrNode := current.GetAnyInstruction ();
        current.ExcludeInstrNode (instrNode);
        newlyCreated := NewPartition (NIL);
        newlyCreated. nextPartition := created;
        newlyCreated.IncludeInstrNode (instrNode);
        created := newlyCreated;
      END;
    END MoveInstrIntoOwnPartition;

  BEGIN
    created := NIL;
    IF (current.Size () > 1) THEN
      (* only partitions with more than one instruction are interesting here *)
      instrNode := current. instrNodeList;
      pivotInstr := instrNode. instr;
      
      IF OwnPartitionAsDefault (pivotInstr) THEN
        (* put every instruction into a partition of their own *)
        MoveInstrIntoOwnPartition (current, created);
      ELSE
        pivotResults := pivotInstr. NumOfResults();
        pivotOperands := pivotInstr. NumOfOperands();      
        
        instrNode := instrNode. nextInstrNode;
        WHILE (instrNode # NIL) DO
          nextInstrNode := instrNode. nextInstrNode;
          moveIt := (instrNode. instr. NumOfOperands() # pivotOperands) OR
                    (instrNode. instr. NumOfResults() # pivotResults);
          IF moveIt THEN
            (* move instruction into another partition *)
            IF (created = NIL) THEN
              created := NewPartition (NIL);
            END;
            current.ExcludeInstrNode (instrNode);
            created.IncludeInstrNode (instrNode);
          END;
          instrNode := nextInstrNode;
        END;
      END;
    END;
  END MoveDifferentSignature;  


PROCEDURE PartitionBySignature;
(* Assure that all instructions within one partition have the same
   number of operands and results.
   Some special instructions are moved into a partition of their own. *)
  BEGIN
    PartitionByPredicate (MoveDifferentSignature);(*    PartitionBySignature; *)
  END PartitionBySignature;


PROCEDURE MoveDifferentOperand (current: Partition; VAR created: Partition);
  VAR
    instrNode, nextInstrNode: InstrNode;
    pivot: D.Instruction;
    instrOpnd, pivotOpnd: D.Opnd;
    moveIt: BOOLEAN;
  BEGIN
    created := NIL;
    instrNode := current. instrNodeList;
    pivot := instrNode. instr;
    
    WHILE (instrNode # NIL) DO
      nextInstrNode := instrNode. nextInstrNode;
      
      pivotOpnd := pivot. opndList;
      instrOpnd := instrNode. instr. opndList;

      moveIt := FALSE;
      WHILE ~moveIt & (pivotOpnd # NIL) DO
        moveIt := ~(((pivotOpnd. arg IS D.Result) = (instrOpnd. arg IS D.Result)) &
                    ( (~(pivotOpnd. arg IS D.Result) & SameOperandArgument (pivotOpnd, instrOpnd)) OR
                      ( (pivotOpnd. arg IS D.Result) & (instrOpnd. arg(D.Result). ResultIndex() = pivotOpnd. arg(D.Result). ResultIndex()))));
        pivotOpnd := pivotOpnd. nextOpnd;
        instrOpnd := instrOpnd. nextOpnd;
      END;
      IF moveIt THEN
        IF created = NIL THEN
          created := NewPartition (NIL);
        END;
        current.ExcludeInstrNode (instrNode);
        created.IncludeInstrNode (instrNode);
      END;
      instrNode := nextInstrNode;
    END;      
  END MoveDifferentOperand;


PROCEDURE PartitionByOperand;
(* Split partitions by their operands. As an operand, all partitions
   must have:
   - the same constant or
   - the same object or
   - the same type or
   - an instruction's result at the same result position. This result must have also
     the same result-index *)
  BEGIN
    PartitionByPredicate (MoveDifferentOperand);
  END PartitionByOperand;


PROCEDURE MoveDifferentLoopDependence (current: Partition; VAR created: PartitionList);
  VAR
    pivotNode, instrNode, nextInstrNode: InstrNode;
  BEGIN
    created := NIL;
    IF (current.Size () > 1) THEN
      pivotNode := current. instrNodeList;
      instrNode := current. instrNodeList. nextInstrNode;
      WHILE (instrNode # NIL) DO
        nextInstrNode := instrNode. nextInstrNode;
        IF (pivotNode. loopMerge # instrNode.loopMerge) THEN
          (* instructions within different loops cannot be substituted by each other *)
          IF created = NIL THEN
            created := NewPartition (NIL);
          END;
          current.ExcludeInstrNode (instrNode);
          created.IncludeInstrNode (instrNode);
        END;
        instrNode := nextInstrNode;
      END;      
    END;
  END MoveDifferentLoopDependence;  


PROCEDURE PartitionByLoopDependence;
  BEGIN
    PartitionByPredicate (MoveDifferentLoopDependence);
  END PartitionByLoopDependence;


PROCEDURE MoveNotAvailable (current: Partition; VAR created: PartitionList);
  VAR
    pivotNode, instrNode, nextInstrNode: InstrNode;
    walk: InstrNode;
  BEGIN
    created := NIL;
    IF (current.Size () > 1) THEN
    
      pivotNode := current. instrNodeList;
      walk := pivotNode. nextInstrNode;
      WHILE (walk # NIL) DO
        IF Available (walk. instr, pivotNode. instr. region) THEN
          pivotNode := walk;
        END;
        walk := walk. nextInstrNode;
      END;
      (* pivot gefunden *)

      instrNode := current. instrNodeList;
      WHILE (instrNode # NIL) DO
        nextInstrNode := instrNode. nextInstrNode;
          
        IF (instrNode # pivotNode) & ~Available (pivotNode. instr, instrNode. instr. region) THEN 
          (* only instructions which are availabe at each other's region can 
              substitute each other *)
          IF (created = NIL) THEN
            created := NewPartition (NIL);
          END;
          current.ExcludeInstrNode (instrNode);
          created.IncludeInstrNode (instrNode);
        END;
          
        instrNode := nextInstrNode;
      END;      
    END;
  END MoveNotAvailable;


PROCEDURE PartitionByAvailability;
  BEGIN
    PartitionByPredicate(MoveNotAvailable);
  END PartitionByAvailability;


PROCEDURE StripUnusedPartitions (VAR partitionList: PartitionList; VAR sizeOnePartitions: PartitionList);
(* remove empty partitions from `partitionList',
   put partitions `p' with one element and `p. usedForSplitting' into
   `sizeOnePartitions' *)   
  VAR
    walk, pre, next: Partition;
  BEGIN
    pre := NIL;
    walk := partitionList;
    WHILE (walk # NIL) DO
      next := walk. nextPartition;
      IF walk.IsEmpty() OR ((walk.Size() = 1) & walk. usedForSplitting) THEN
        (* remove empty partition *)
        IF (pre = NIL) THEN
          partitionList := walk. nextPartition;
        ELSE
          pre. nextPartition := walk. nextPartition;
        END;
        IF (walk.Size () = 1) THEN
          walk. nextPartition := sizeOnePartitions;
          sizeOnePartitions := walk;
        END;
      ELSE
        pre := walk;
      END;
      walk := next;
    END;
  END StripUnusedPartitions;


PROCEDURE GetMaxOpndPos (instrList: InstrList): LONGINT;
(* get the maximum operand position *)
  VAR
    max: LONGINT;
    use: D.Opnd;
    result: D.Result;
    currentInstr: InstrList;
  BEGIN
    max := -1;
    currentInstr := instrList;
    WHILE (currentInstr # NIL) DO
      result := currentInstr. instr;
      WHILE (result # NIL) DO
        use := result. useList;
        WHILE (use # NIL) DO
          IF (use. OperandIndex() > max) THEN
            max := use. OperandIndex();
          END;
          use := use. nextUse;
        END;
        result := result. nextResult;
      END;
      currentInstr := currentInstr. nextInstrList;
    END;
    RETURN max;
  END GetMaxOpndPos;       

PROCEDURE GetSplittedPartitions (VAR splittedPartitions: Partition; instrList: InstrList; opndPos: LONGINT);
  VAR
    currentInstr: InstrList;
    use: D.Opnd;
    result: D.Result;
      (* find out, which partitions must be splitted by `current' *)
  BEGIN
    splittedPartitions := NIL;
    currentInstr := instrList;
    WHILE (currentInstr # NIL) DO
      result := currentInstr. instr;
      WHILE (result # NIL) DO
        use := result. useList;
        WHILE (use # NIL) DO
          IF (use. OperandIndex() = opndPos) THEN
            AddToWorklistUnique (splittedPartitions, use. instr. info(InstrNode). partition);
          END;
          use := use. nextUse;
        END;
        result := result. nextResult;
      END;
      currentInstr := currentInstr. nextInstrList;
    END;
  END GetSplittedPartitions;

PROCEDURE HasOpndAtIn (instr: D.Instruction; at: LONGINT; in: InstrList): BOOLEAN;
  VAR
    opnd: D.Opnd;
    opndInstr: D.Instruction;
    result: BOOLEAN;
    walk: InstrList;
  BEGIN
    opnd := instr. NthOperand (SHORT(at));
    opndInstr := opnd. arg(D.Result). instr;

    result := FALSE;
    walk := in;
    WHILE ~result & (walk # NIL) DO
      result := (walk. instr = opndInstr);
      walk := walk. nextInstrList;
    END;
    RETURN result;
  END HasOpndAtIn;      


PROCEDURE SplitPartitions;
  VAR
    fixpoint: BOOLEAN;
    newParts: PartitionList;
    createdParts: PartitionList;
    current: Partition;
    
  PROCEDURE SplitByPartition (splittingPart: Partition; VAR created: PartitionList);
    VAR
      maxOpndPos, opndPos: LONGINT;
      instrList: InstrList;
      splittedPartitions: PartitionList;
      walk: Partition;
    
    PROCEDURE SplitPartitionByAt (split: Partition; by: Partition; at: LONGINT; instrList: InstrList);
      VAR
        instrNode: InstrNode;
        subIncl, subExcl: Partition;
      BEGIN
        IF (split.Size () > 1) THEN
          subIncl := NewPartition (split);
          subExcl := NewPartition (split);
          split. splittedBy := by;
          split. atOpndPos := at;
          
          WHILE ~split.IsEmpty () DO
            instrNode := split.GetAnyInstruction ();
            split.ExcludeInstrNode (instrNode);
            IF HasOpndAtIn (instrNode. instr, at, instrList) THEN
              subIncl.IncludeInstrNode (instrNode);
            ELSE
              subExcl.IncludeInstrNode (instrNode);
            END;
          END;
          
          IF subExcl.IsEmpty () THEN
            subExcl := NIL;
            subIncl. usedForSplitting := split. usedForSplitting;
          ELSE
            subExcl. nextPartition := created;
            created := subExcl;
          END;

          IF subIncl.IsEmpty () THEN
            subIncl := NIL;
            subExcl. usedForSplitting := split. usedForSplitting;
          ELSE
            subIncl. nextPartition := created;
            created := subIncl;
          END;
          
          IF (subIncl # NIL) & (subExcl # NIL) THEN
            fixpoint := FALSE;
          END;
        END;
      END SplitPartitionByAt;
    
    
    BEGIN
      instrList := current.CreateInstrList ();
      maxOpndPos := GetMaxOpndPos (instrList);
      
      splittedPartitions := NIL;
      FOR opndPos := 0 TO (maxOpndPos + 1) DO
        GetSplittedPartitions (splittedPartitions, instrList, opndPos);
        
        IF PartitionInWorklist (current, splittedPartitions) THEN
          (* self split *)
          SplitPartitionByAt (current, current, opndPos, instrList);
          ClearWorklist (splittedPartitions);
          RETURN; (* abort this iteration *)
        ELSE
          walk := splittedPartitions;
          WHILE (walk # NIL) DO
            SplitPartitionByAt (walk, current, opndPos, instrList);
            walk := walk. tmpLink;
          END;
        END;
        
        ClearWorklist (splittedPartitions);
      END;
      current. usedForSplitting := TRUE;
    END SplitByPartition;
  
  BEGIN
    REPEAT
      fixpoint := TRUE;
      createdParts := NIL;
      StripUnusedPartitions (partitionList, sizeOnePartitions);
      current := partitionList;
      WHILE (current # NIL) DO
        IF ~current.usedForSplitting & ~current.IsEmpty () THEN
          newParts := NIL;
          SplitByPartition (current, newParts);

          IF (newParts # NIL) THEN
            IF (createdParts = NIL) THEN
              createdParts := newParts;
            ELSE
              newParts.Concatenate (createdParts);
              createdParts := newParts;
            END;
          END;
        END;
        
        IF (current. nextPartition = NIL) & (createdParts # NIL) THEN
          (* concatenate partitionList with createdParts *)
          partitionList.Concatenate (createdParts); (* current. nextPartition := createdParts; *)
          createdParts := NIL;
        END;
        current := current. nextPartition;
      END;
    UNTIL fixpoint;
  END SplitPartitions;


PROCEDURE CSE;
(* PRE: 
    All collections in `partitionList' do only contain those instructions which
    are considered equivalent, i.e. all three splitting processes
    were run on them.
    
   For every partition in `partitionList' all instructions are inspected if
   one dominated others. If yes, then replace all uses of the dominated
   instructions by the dominating one.
   
   If of two instruction none dominates the other, then both are
   independent and must be preserved. *)  

  VAR
    partWalk: Partition;
    other: Partition;
  
  PROCEDURE Eliminate (part: Partition);
    VAR
      pivotNode, instrNode: InstrNode;
      pivot, instr: D.Instruction;
      pivotRes, instrRes: D.Result;
    BEGIN
      IF (part.Size () > 1) THEN
        pivotNode := part.GetAnyInstruction ();
        part.ExcludeInstrNode (pivotNode);
        pivot := pivotNode. instr;
        
        WHILE ~(part.IsEmpty ()) DO
        (* get two instructions and replace one by the other.
           "the other" will be added to the list again *)
          instrNode := part.GetAnyInstruction ();
          part.ExcludeInstrNode (instrNode);
          IF Available (pivot, instrNode. instr. region) THEN
            other.IncludeInstrNode (instrNode);
          ELSE
            other.IncludeInstrNode (pivotNode);
            pivotNode := instrNode;
            pivot := pivotNode. instr;
          END;
        END;
    
        (* pivot dominates all instructions in `other', so replace them by pivot *)
        WHILE ~(other.IsEmpty ()) DO
          instrNode := other.GetAnyInstruction ();
          other.ExcludeInstrNode (instrNode);
          instr := instrNode. instr;
          instrRes := instr;
          pivotRes := pivot;
          WHILE (instrRes # NIL) DO              
            instrRes. ReplaceUses (pivotRes);
            instrRes := instrRes. nextResult;
            pivotRes := pivotRes. nextResult;
          END;
          instr. Delete();
        END;
      END;
    END Eliminate;

  BEGIN
    other := NewPartition (NIL);
    partWalk := partitionList;
    WHILE (partWalk # NIL) DO
      Eliminate (partWalk);
      partWalk := partWalk. nextPartition;
    END;
  END CSE;


PROCEDURE Number* (greg: D.Region);
    
  BEGIN
    Normalize (greg);
    
    InitCollectPartitions;
    ClassifyInstructions (greg);
    CollectNonEmptyPartitions;
    InitCollectPartitions; (* for garbage collection *)
    
    greg(D.GlobalRegion). NumberDominanceTree();
    MarkLoopDependentInstr (greg);

    PartitionBySignature;
    PartitionByOperand;
    PartitionByLoopDependence;

    SplitPartitions;

    PartitionByAvailability;

    CSE; 
  END Number;
  
END ValueNumbering.
