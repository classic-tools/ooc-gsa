(*	$Id: Schedule.Mod,v 1.36 2000/12/27 16:33:57 ooc-devel Exp $	*)
MODULE Schedule;
(*  Instruction scheduler for ANSI-C back-end.
    Copyright (C) 1996-2000  Michael van Acken

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
<* DEFINE Schedule_DEBUG := FALSE *>

IMPORT
  <* IF Schedule_DEBUG THEN *> WriteGSA, Out, <* END *>
  D := Data, Opc := Opcode, GuardCond, Sym := SymbolTable, StdTypes, 
  Class := Classify, Alias := AliasAnalysis, Worklist;


(*
The scheduling algorithm is divided into the following steps:

1.  Resolve anti-dependencies by introducing explicit data
dependencies.  The reason for these anti-dependencies is that on GSA
level every result is a distinct copy, but in the target code some
results are mapped onto the same memory location, i.e. only a single
copy of this value exists ever.  All structured values (records,
arrays and possibly complex values) and nonlocal values (everything in
$store) exist only once in the running program.  This means that write
instructions to a part of the structured value or to a nonlocal
variable have to be delayed until all read operations on the old value
(the one existing before the change) have been completed.  This
restriction isn't modeled in the GSA code and has to be added to the
code by appending additional operands to update instructions, one for
every read instruction on the updated value. 

2.  Make sure that all results that are used after a region has been left are
actually computed before this happens.  Take for example the backedge guard of
a loop or a guard of a conditional expression.  These guards serve as operands
of a merge instruction, meaning that control continues in the merge after the
guard has been completed.  If the respective branch into the merge is taken,
then the gate operands (of the gates of the merge) contain the current values
that are visible after the branch.  To make sure that these values are actually
computed the (calculation of the) arguments of the gates have to be scheduled
_before_ the branches.  This is implemented by adding them for the duration of
the scheduling as pseudo operands to the branches.

3.  Make hidden dependencies between regions explicit.  This means that for the
following situation
   (5) region A
      (6) instr 
   (7) region B
      (8) instr (6)
the dependence of instruction (8) on instruction (6) is turned into a
dependence of region (7) on region (5).  This is done to simplify the
topological sort in step 4, since all regions can then be scheduled bottom up
(i.e. nested regions first) and the special case of indirect dependencies is
integrated smoothly into the general algorithm.

4.  Run a topological sort on all instructions.  This changes the half order of
the plain GSA code into a strict sequence of instructions.  All instructions
that a given instruction depends on are placed before this instruction.
Regions that contribute an argument to a (non-loop) merge instruction are
treated specially.  They aren't scheduled on their own, but as a single block
together with their merge instruction.  This ensures that a merge is directly
placed behind its input regions and that no instructions are scheduled between
the input regions.

5.  Cleanup.  Remove all auxiliary data that has been installed in the previous
steps. 

*)

TYPE
  ScheduleInfo = POINTER TO ScheduleInfoDesc;
  ScheduleInfoDesc = RECORD
    (D.InfoDesc);
    value: LONGINT;
    inWorklist: BOOLEAN;
    next: ScheduleInfo;
  END;

CONST
  maxValue = MAX (LONGINT);
  minValue = 0;
  
CONST
  markerScheduled = -1;
  markerDelayed = -2;
  
VAR
  auxObj: D.Object;
  auxLocation: D.SymLocation;
  (* this value is used for the location attributes of operands created by this
     module; it identifies all auxiliary operands that are inserted to make any
     hidden dependencies explicit and that should be removed when the 
     scheduling is done *)
  ready: D.Region;
  (* auxiliary region to hold the set of schedulable instruction (ready set)
     while executing procedure `Schedule' *)
  infoList: ScheduleInfo;
  (* list of "old" info structures; filled by procedure `Select', and 
     `InitSelection' tries to take objects from it *)


PROCEDURE DataDependencies (greg: D.GlobalRegion; r: D.Region);
(* Introduce operand nodes to resolve anti-dependencies.  This means that 
   writing (update) instructions get additional operands refering to all 
   reading (access) instructions on the same memory location with the old 
   value.  This effectivly delays the writing instruction until all reads
   have finished.  This corresponds to step 1 in the above description.  *)
  VAR
    instr: D.Instruction;
  
  PROCEDURE AddAccesses (update: D.Instruction; value: D.Usable);
  (* Adds all access instructions that read `value' (and all access 
     instructions reading the access instruction) as arguments to `update'. *)
    VAR
      use: D.Opnd;
      m, n: INTEGER;
      access: D.Instruction;
    BEGIN
      IF (value IS D.Object) THEN
        (* ignore undefined variables *)
        RETURN
      ELSIF (value IS D.Instruction) &
         (value(D.Instruction). opcode = Opc.gate) &
         (value(D.Instruction). opndList. arg(D.Merge). opcode = Opc.mergeLoop) THEN
        (* make `update' also depend on all access instructions that read the
           second argument (entering operand) of the loop gate *)
        AddAccesses (update, value(D.Instruction). opndList. nextOpnd. arg)
      ELSIF (value IS D.Instruction) &
            ((value(D.Instruction). opcode = Opc.typeGuard) OR
             (value(D.Instruction). opcode = Opc.typeAssert)) THEN
        (* make `update' also depend on all instructions that read the first 
           argument of a type guard *)
        AddAccesses (update, value(D.Instruction). opndList. arg)
      END;

      use := value. useList;
      WHILE (use # NIL) DO      
        IF (use. location # auxLocation) &
           ((use. instr. opcode DIV Opc.sizeClass = Opc.classAccess) OR
            (use. instr. opcode = Opc.stringCopy) OR
            (use. instr. opcode = Opc.structCopy) OR
            (use. instr. opcode = Opc.call)) &
           ~GuardCond.Contradicting(update. region. info(GuardCond.RegionInfo),
                           use. instr. region. info(GuardCond.RegionInfo)) &
           (Alias.Aliasing (update, Alias.onlyUpdate, 
                        use. instr, Alias.accessOrUpdate) # Alias.noAlias) THEN
          n := use. OperandIndex();
          CASE use. instr. opcode OF
          | Opc.accessField, Opc.accessElement:
            m := 0
          | Opc.stringCopy, Opc.structCopy:
            m := 3
          | Opc.accessNonlocal, Opc.accessVarParam, Opc.accessHeap:
            m := 2
          | Opc.accessMem:
            m := 1
          | Opc.call:
            m := -1
          END;
          IF (m = n) OR (m < 0) THEN
            (* add dependencies to the access `use. instr' to `update' and to
               all accesses that are funneled through `use. instr'  *)
            access := use. instr;
            IF ~(Class.instrNoOutput IN access. flags) &
               (update # access) & 
               (Alias.Aliasing (update, Alias.onlyUpdate, 
                            access, Alias.accessOrUpdate) # Alias.noAlias) THEN
              (* don't add operand if `update' is a collect belonging to 
                 `access' (this would cause a cyclic dependence), or if one of
                 the instructions doesn't produce any output code, or if access
                 and update do not alias *)
              update. UniqueOperand (access, auxLocation)
            END;
            IF (access. opcode DIV Opc.sizeClass = Opc.classAccess) &
               (Class.instrNoOutput IN access. flags) THEN
              AddAccesses (update, access)
            END
          END
        END;
        use := use. nextUse
      END
    END AddAccesses;
  
  PROCEDURE AddStoreAccesses (update: D.Instruction; value: D.Usable);
  (* The updated variable is $store; since the instruction that defined the 
     current value of this variable  might not have overwritten the value 
     changed by the update `instr' all access instructions reading the old 
     value of $store have to be completed before `instr', too.  *)
    VAR
      opnd: D.Opnd;
      skipLast: BOOLEAN;
      store: D.Instruction;
      
    PROCEDURE GetStoreInput (instr: D.Instruction): D.Usable;
      VAR
        opnd: D.Opnd;
      BEGIN
        CASE instr. opcode OF
        | Opc.call, Opc.accessMem, Opc.updateMem, Opc.move:
          opnd := instr. GetOperand (Sym.store, D.symLocObject)
        | Opc.updateNonlocal, Opc.updateVarParam, Opc.updateHeap:
          opnd := instr. NthOperand (2)
        END;
        RETURN opnd. arg
      END GetStoreInput;

    BEGIN
      IF (value(D.Result). info = update) THEN
        RETURN  (* `value' has already been visited *)
      ELSE
        value(D.Result). info := update
      END;
      
      store := value(D.Result). instr;
      AddAccesses (update, value);
      IF ~Alias.TransitiveStoreAlias (update, store) THEN
        IF (store. opcode # Opc.createStore) &
           ~GuardCond.Contradicting (
                    update. region. info(GuardCond.RegionInfo),
                    store. region. info(GuardCond.RegionInfo)) &
           (Alias.Aliasing (update, Alias.onlyUpdate, 
                            store, Alias.accessOrUpdate) # Alias.doAlias) THEN
          IF (store. opcode = Opc.gate) THEN
            skipLast := (store.opndList.arg(D.Merge).opcode = Opc.mergeLoop);
            opnd := store. opndList. nextOpnd;
            WHILE (opnd # NIL) & (~skipLast OR (opnd. nextOpnd # NIL)) DO
              AddStoreAccesses (update, opnd. arg);
              opnd := opnd. nextOpnd
            END
          ELSE
            AddStoreAccesses (update, GetStoreInput (store))
          END
        END
      END
    END AddStoreAccesses;
  
  PROCEDURE InspectUpdate (instr, originalUpdate: D.Instruction);
    VAR
      up: D.Instruction;
      res: D.Result;
      loc: D.Location;
      opnd: D.Opnd;
      
    PROCEDURE UpUpdate (instr: D.Instruction): D.Instruction;
    (* If `instr' is passed as new value to an update instruction, return this
       next higher update.  Otherwise return NIL.  *)
      VAR
        use: D.Opnd;
      BEGIN
        use := instr. useList;
        WHILE (use # NIL) DO
          IF (use. nextOpnd = NIL) &
             (use. instr. opcode DIV Opc.sizeClass = Opc.classUpdate) THEN
            RETURN use. instr
          END;
          use := use. nextUse
        END;
        RETURN NIL
      END UpUpdate;
    
    PROCEDURE UpdatedValue (instr: D.Instruction): D.Usable;
      BEGIN
        CASE instr. opcode OF
        | Opc.updateField, Opc.updateElement:
          RETURN instr. opndList. arg
        | Opc.updateHeap, Opc.updateNonlocal, 
          Opc.updateVarParam, Opc.updateMem:
          RETURN instr. opndList. nextOpnd. nextOpnd. arg
        END
      END UpdatedValue;
    
    BEGIN
      (* if `instr' is an update instruction, add all access instructions 
         reading the original value, i.e. the one that will be destroyed by 
         the update, as operands to the update *)
      CASE instr. opcode OF
      | Opc.updateField, Opc.updateElement:
        AddAccesses (originalUpdate, instr. opndList. arg);
        up := UpUpdate (instr);
        IF (up # NIL) THEN
          InspectUpdate (up, originalUpdate)
        END
      | Opc.updateNonlocal, Opc.updateVarParam, Opc.updateHeap:
        AddStoreAccesses (originalUpdate, instr. NthArgument (2))
      | Opc.updateMem:
        AddAccesses (originalUpdate, instr. NthArgument (2))
      | Opc.stringCopy, Opc.structCopy:
        AddAccesses (originalUpdate, instr. opndList. arg);
        up := UpUpdate (instr);
        IF (up # NIL) THEN
          InspectUpdate (up, originalUpdate)
        END
      | Opc.call:  
        (* check if call writes to $store *)
        res := instr. GetResult (Sym.store, D.symLocObject);
        IF (res = NIL) THEN
          res := instr. GetResult (Sym.mem, D.symLocObject)
        END;
        IF (res # NIL) THEN  (* $store is modified *)
          opnd := instr. GetOperand (Sym.store, D.symLocObject);
          IF (opnd = NIL) THEN
            opnd := instr. GetOperand (Sym.mem, D.symLocObject);
            opnd := opnd. arg(D.Instruction). GetOperand (Sym.store, D.symLocObject)
          END;
          IF (instr = originalUpdate) THEN
            AddStoreAccesses (opnd. instr, opnd. arg)
          ELSE
            AddStoreAccesses (originalUpdate, opnd. arg)
          END
        END;

        (* check if call modifies structured local variables of the caller *)
        res := instr. nextResult;
        WHILE (res # NIL) DO
          loc := res. location;
          IF (loc # NIL) & 
             (loc(D.SymLocation). attrib = D.symLocObject) &
             (loc(D.SymLocation). var IS D.Object) &
             (loc(D.SymLocation). var(D.Object). localTo = greg. bodyOf) &
             StdTypes.PassPerReference (loc(D.SymLocation). var(D.Object), FALSE) THEN
            opnd := instr. GetOperand (loc(D.SymLocation). var, D.symLocObject);
            AddAccesses (originalUpdate, opnd. arg)
          ELSIF (res. useList # NIL) &
                ((res. useList. instr. opcode = Opc.updateField) OR
                 (res. useList. instr. opcode = Opc.updateElement)) &
                (res. useList. OperandIndex() = 3) &
                (Class.instrNoOutput IN res. useList. instr. flags) THEN
            (* side effect of procedure call (i.e., an instruction result that
               is not the instruction itself) modifies a value; the update
               instruction must be a "no op", i.e., it must represent a
               change made by the called procedure, and not change some
               variable itself *)
            AddAccesses (instr, UpdatedValue (res. useList. instr))
          END;
          res := res. nextResult
        END
      ELSE  (* ignore *)
      END
    END InspectUpdate;
  
  BEGIN
    instr := r. instrList;
    WHILE (instr # NIL) DO
      IF (instr IS D.Region) THEN
        DataDependencies (greg, instr(D.Region))
      ELSIF ~(Class.instrNoOutput IN instr. flags) THEN
        InspectUpdate (instr, instr)
      END;
      instr := instr. nextInstr
    END
  END DataDependencies;

PROCEDURE BranchDependencies (r: D.Region);
  VAR
    r0: D.Region;
    merge: D.Merge;
    use: D.Opnd;
    gateArg: D.Usable;
    opn: INTEGER;
  BEGIN
    (* handle nested regions *)
    r0 := r. regionList;
    WHILE (r0 # NIL) DO
      BranchDependencies (r0);
      r0 := r0. nextRegion
    END;
    
    merge := r. RegionMerge();
    IF (merge # NIL) THEN  
      (* control passes from `r' into `merge': scan all gates belonging to
         `merge' *)
      opn := merge. ArgumentIndex (r)+1;
      use := merge. useList;
      WHILE (use # NIL) DO
        IF (use. instr. opcode = Opc.gate) THEN
          gateArg := use. instr. NthArgument (opn);
          IF (gateArg IS D.Result) & 
             ~r. Dominates (gateArg(D.Result). instr. region) THEN
            (* the argument isn't a constant value and it isn't calculated in
               region `r': add the value as operand to `r' *)
            r. UniqueOperand (gateArg, auxLocation)
          END
        END;
        use := use. nextUse
      END
    END
  END BranchDependencies;

PROCEDURE BackedgeOpnd (opnd: D.Opnd): BOOLEAN;
(* Result is TRUE iff `opnd' corresponds to the backedge operand of a loop 
   gate.  *)
  BEGIN
    RETURN (opnd. nextOpnd = NIL) &
           (opnd. instr. opcode = Opc.gate) &
           (opnd. instr. opndList. arg(D.Merge). opcode = Opc.mergeLoop)
  END BackedgeOpnd;

PROCEDURE RegionDependencies (r: D.Region);
(* Add additional dependencies to and from regions caused by data dependencies
   nested in those regions.  See step 3 in the above description.  *)
  VAR
    instr, instrBase, useBase: D.Instruction;
    use: D.Opnd;
    res: D.Result;
  
  PROCEDURE GetNeighbours (i0, i1: D.Instruction; 
                           VAR base0, base1: D.Instruction);
  (* Finds the two base instructions that appear in the same region and 
     contain the respective given instructions.
     pre: ~dominates(i0, i1) & ~dominates(i1, i0)
     post: (base0. region = base1. region) & (base0 # base1) &
           ((base0 = i0) OR (dominates(base0, i0))) &
           ((base1 = i1) OR (dominates(base1, i1)))  *)
    BEGIN
      base0 := i0; base1 := i1;
      WHILE (base0. region # base1. region) DO
        IF base0. region. Dominates (base1. region) THEN
          base1 := base1. region
        ELSE
          base0 := base0. region
        END
      END
    END GetNeighbours;
  
  BEGIN
    instr := r. instrList;
    WHILE (instr # NIL) DO
      IF (instr IS D.Region) THEN  (* handled nested regions *)
        RegionDependencies (instr(D.Region))
      END;
      
      (* inspect places of uses of this instruction *)
      res := instr;
      WHILE (res # NIL) DO
        (* inspect all uses of `res'; if for every use of `res' that ins't
           part of the region of `instr' add a new dependence *)
        use := res. useList;
        WHILE (use # NIL) DO
          IF (use. instr. opcode # Opc.mergeLoop) &
             (use. instr. region # instr. region) &
             ~BackedgeOpnd (use) &
             ~((instr IS D.Region) &
               instr(D.Region). Dominates (use. instr. region)) THEN
            GetNeighbours (instr, use. instr, instrBase, useBase);
            useBase. UniqueOperand (instrBase, auxLocation)
          END;
          use := use. nextUse
        END;
        res := res. nextResult
      END;
      instr := instr. nextInstr;
    END;
  END RegionDependencies;


(* The ANSI-C backend has only a very limited influence on the generated 
   executable.  Therefore scheduling is a rather simple matter.  For every
   instruction appearing in the output the length of the path to the region's
   end, the number of uses, and the number of operands contribute to the 
   scheduling heuristics.  *)
   
PROCEDURE InitSelection (r: D.Region);
(* Initializes data structures used by procedure `Select' below.  This data is
   added to every instruction in `r', excluding all instructions in nested 
   regions.  This procedure is called before the very first ready set is 
   build.  *)
  VAR
    instr, prev: D.Instruction;
    list: Worklist.Worklist;
    info: D.Info;
    val, size: LONGINT;
    use, opnd: D.Opnd;
    region: D.Region;
  CONST
    sizeMergeLoop = 5000;
    sizeRegion = 1000;
    
  PROCEDURE NewScheduleInfo (): ScheduleInfo;
    VAR
      info: ScheduleInfo;
    BEGIN
      IF (infoList = NIL) THEN
        NEW (info)
      ELSE
        info := infoList;
        infoList := infoList. next
      END;
      info. value := 0;
      info. inWorklist := FALSE;
      RETURN info
    END NewScheduleInfo;
  
  PROCEDURE EndOfRegion (instr: D.Instruction): BOOLEAN;
  (* TRUE iff all uses of `instr' are outside region `r'.  *)
    VAR
      use: D.Opnd;
    BEGIN
      use := instr. useList;
      WHILE (use # NIL) DO
        IF ~use. instr. region. Dominates (r) THEN
          RETURN FALSE
        END;
        use := use. nextUse
      END;
      RETURN TRUE
    END EndOfRegion;
  
  BEGIN
    (* initialize path counter of every instruction; all instructions that do
       not provide any arguments for instructions in `r' will be placed in the
       worklist *)
    list. Init;
    instr := r. instrList;
    WHILE (instr # NIL) DO
      instr. info := NewScheduleInfo();
      IF (instr. useList = NIL) & (D.instrNotDead IN instr. flags) THEN
        instr. info(ScheduleInfo). value := maxValue
      ELSIF EndOfRegion (instr) THEN
        list. AddHead (instr);
        instr. info(ScheduleInfo). inWorklist := TRUE
      END;
      instr := instr. nextInstr
    END;
    
    (* calculate path length of all instructions *)
    WHILE ~list. IsEmpty() DO
      info := list. GetHead();
      list. RemoveHead;
      instr := info(D.Instruction);
      instr. info(ScheduleInfo). inWorklist := FALSE;
      
      IF (instr. opcode = Opc.mergeLoop) THEN
        size := sizeMergeLoop
      ELSIF (instr IS D.Region) THEN
        size := sizeRegion
      ELSIF (Class.instrNoOutput IN instr. flags) THEN
        size := 0
      ELSE
        size := 1
      END;
      val := instr. info(ScheduleInfo). value+size;

      IF (instr. opcode = Opc.mergeLoop) THEN
        opnd := instr. opndList. nextOpnd. nextOpnd
      ELSIF (instr. opcode = Opc.gate) &
            (instr. opndList. arg(D.Merge). opcode = Opc.mergeLoop) THEN
        opnd := instr. opndList. nextOpnd. nextOpnd. nextOpnd
      ELSE
        opnd := instr. opndList
      END;
      WHILE (opnd # NIL) DO
        IF (opnd. arg IS D.Result) &
           (opnd. arg(D.Result). instr. region = r) THEN
          prev := opnd. arg(D.Result). instr;
          IF (val > prev. info(ScheduleInfo). value) THEN
            prev. info(ScheduleInfo). value := val;
            IF ~prev. info(ScheduleInfo). inWorklist THEN
              (*DEBUG: if scheduler hangs comment out the following two lines
                 and uncomment the output stuff at the end of procedure 
                 `Schedule' *)
<* IF ~Schedule_DEBUG THEN *>
              list. AddTail (prev);
              prev. info(ScheduleInfo). inWorklist := TRUE
<* END *>
            END
          END
        END;
        opnd := opnd. nextOpnd
      END
    END;
    region := r. regionList;
    WHILE (region # NIL) DO
      IF (region. opcode = Opc.mergeLoop) THEN
        INC (region. info(ScheduleInfo). value, sizeMergeLoop)
      ELSE
        INC (region. info(ScheduleInfo). value, sizeRegion)
      END;
      region := region. nextRegion
    END;
    
    (* do some fine tuning on the instruction values *)
    instr := r. instrList;
    WHILE (instr # NIL) DO
      IF (Class.instrNoOutput IN instr. flags) THEN
        instr. info(ScheduleInfo). value := maxValue
      ELSIF (instr. opcode = Opc.exit) THEN
        (* exit must be scheduled as last instruction, since it inserts a 
           "return" into the C code; to move it to the very end, it is given
           the smallest value of all instructions *)
        instr. info(ScheduleInfo). value := minValue-1
      ELSE
        val := instr. info(ScheduleInfo). value;
        (* prefer instructions with more uses *)
        use := instr. useList;
        WHILE (use # NIL) DO
          IF (use. location # auxLocation) THEN
            INC (val)
          END;
          use := use. nextUse
        END;
        (* prefer instructions with many operands in registers *)
        opnd := instr. opndList;
        WHILE (opnd # NIL) & (opnd. location # auxLocation) DO
          IF (opnd. arg IS D.Instruction) &
             ~(Class.instrNoOutput IN opnd. arg(D.Instruction). flags) THEN
            INC (val)
          END;
          opnd := opnd. nextOpnd
        END;
        instr. info(ScheduleInfo). value := val
      END;
      instr := instr. nextInstr
    END
  END InitSelection;

PROCEDURE JustAdded (ready: D.Region; instr: D.Instruction);
(* Called just after `instr' has been added to the ready list (that is, to
   region `ready').  Useful to maintain a local order in `ready' to increase
   the efficiency of the `Select' procedure below.  This procedure maintains
   the list of ready instructions sorted by decreasing value.  *)
  VAR
    i: D.Instruction;
    val: LONGINT;
  BEGIN
    val := instr. info(ScheduleInfo). value;
    (* `instr' is the last element in `ready.instrList' *)
    i := ready. instrList;
    WHILE (i. info(ScheduleInfo). value >= val) & (i # instr) DO
      i := i. nextInstr
    END;
    IF (i # instr) THEN
      instr. MoveInFront (i)
    END
  END JustAdded;

PROCEDURE Select (ready: D.Region): D.Instruction;
(* Select an instruction for scheduling from the current ready set; the 
   selection function implemented is rather simple, it takes the instruction
   with the maximum value.  The value is statically determined by 
   `InitSelection' and `JustAdded' does the sorting for us.  *)
  VAR
    info: ScheduleInfo;
  BEGIN
    info := ready. instrList. info(ScheduleInfo);
    info. next := infoList;
    infoList := info;
    ready. instrList. info := NIL;
    RETURN ready. instrList
  END Select;


PROCEDURE Schedule (r: D.Region);
(* Schedules instructions in `r'.  See step 4 in the above description.  *)
  VAR  
    instr, scheduled: D.Instruction;
    nested: D.Region;
    opnd: D.Opnd;
    skipLast: BOOLEAN;
    unscheduled: LONGINT;
  
  PROCEDURE MergeUse (instr, use: D.Instruction): BOOLEAN;
  (* Returns TRUE iff `instr' is a region that contributes to the merge `use'.
     If `instr' isn't a region, `use' is a gate or a loop merge, `use' is not
     on the level `r', or `instr' does not merge into `use', then the result is
     FALSE.  *)
     
    PROCEDURE MergeOpnd (merge: D.Merge; region: D.Region): BOOLEAN;
    (* Returns TRUE iff `region' represents one of the original operands of the
       merge, or is indirectly part of such an operand.  *)
      VAR
        arg, reg: D.Region;
        opnd: D.Opnd;
      BEGIN
        opnd := merge. opndList;
        WHILE (opnd # NIL) & (opnd. location # auxLocation) DO
          arg := opnd. arg(D.Region);
          IF region. Dominates (arg) THEN
            RETURN TRUE
          ELSE
            reg := arg;
            WHILE (reg. region # r) DO
              reg := reg. region
            END;
            IF (reg IS D.Merge) & (reg. opcode # Opc.mergeLoop) &
               MergeOpnd (reg(D.Merge), region) THEN
              RETURN TRUE
            END
          END;
          opnd := opnd. nextOpnd
        END;
        RETURN FALSE
      END MergeOpnd;
    
    BEGIN
      IF ~(Class.instrDelayedRegion IN instr. flags) OR
         ~(use IS D.Merge) OR (use. opcode = Opc.mergeLoop) OR
         (use. region # r) THEN
        RETURN FALSE
      ELSE
        RETURN ((use.opcode # Opc.mergeLoop) OR (use.opndList.arg # instr)) &
               MergeOpnd (use(D.Merge), instr(D.Region))
      END
    END MergeUse;
  
  PROCEDURE AddToReady (instr: D.Instruction): D.Instruction;
  (* Adds `instr' to the set of schedulable instructions.
     result: First instruction following `instr' that hasn't been moved into 
       the `ready' region.  *)
    VAR
      use: D.Opnd;
      next: D.Instruction;
    BEGIN
      IF (Class.instrDelayedRegion IN instr. flags) THEN
        (* this region is scheduled as part of a merge; it's not added to the
           ready set, but the dependence counters of the merges depending on it
           are decremented by one, maybe adding the merge to the ready set *)
        use := instr. useList;
        WHILE (use # NIL) DO
          IF MergeUse (instr, use. instr) THEN
            DEC (use. instr. marker);
            IF (use. instr. marker = 0) THEN
              next := AddToReady (use. instr)
            END
          END;
          use := use. nextUse
        END;
        instr. marker := markerDelayed;
        RETURN instr. nextInstr
      ELSE
        (* move `instr' into the special region `ready'; keep in mind that, 
           although basically all instruction belong to region `r', part of 
           them resides temporarily in `ready'; therefore the `region' 
           attribute of a given instruction has to be used with care in
           boolean expressions *)
        next := instr. nextInstr;
        ready. MoveInstruction (instr);
        JustAdded (ready, instr);
        RETURN next
      END
    END AddToReady;
  
  PROCEDURE ScheduleInstr (instr: D.Instruction);
  (* Appends `instr' to the list of already scheduled instructions.  
     pre: instr. marker = 0  *)
    VAR
      res: D.Result;
      next: D.Instruction;
      use: D.Opnd;
      
    PROCEDURE ScheduleMergeOpnds (merge: D.Instruction);
    (* Schedules the regions converging into the given merge.
       pre: merge. marker >= 0  *)
      VAR
        opnd: D.Opnd;

      PROCEDURE Schedulable (opnd: D.Opnd): BOOLEAN;
        BEGIN
          RETURN (opnd. arg IS D.Result) &
                 (opnd. arg(D.Result). instr. region = r) &
                 (opnd. arg(D.Result). instr. marker # markerScheduled)
        END Schedulable;

      BEGIN
        IF (merge. opndList. arg(D.Region). opcode = Opc.guardTrue) &
           Schedulable (merge. opndList) &
           Schedulable (merge. opndList. nextOpnd) THEN
          (* place the if-false guard in front of the if-true guard; this 
             shouldn't make any difference, except for the ANSI-C back-end
             where it save some negations in the emitted code *)
          ScheduleInstr (merge. opndList. nextOpnd. arg(D.Instruction));
          ScheduleInstr (merge. opndList. arg(D.Instruction))
        ELSE
          opnd := merge. opndList;
          WHILE (opnd # NIL) DO
            IF Schedulable (opnd) THEN
              ScheduleInstr (opnd. arg(D.Instruction))
            END;
            opnd := opnd. nextOpnd
          END
        END
      END ScheduleMergeOpnds;

    BEGIN
      IF ~(Class.instrDelayedRegion IN instr. flags) THEN
        (* move instruction from region `ready' into region `r' *)
        r. MoveInstruction (instr)
      END;
      IF (instr IS D.Merge) & (instr. opcode # Opc.mergeLoop) THEN
        (* place the merged regions in front of the merge *)
        ScheduleMergeOpnds (instr)
      END;
      
      instr. MoveBehind (scheduled);
      scheduled := instr;
      instr. marker := markerScheduled;
      DEC (unscheduled);
      
      (* for every result of the instruction decrement the dependence counter
         of all instructions using it; ignore uses in `instr' itself 
         (pathological loops), the merge of a delayed region (has already
         been decremented in AddToRead), uses in instructions outside of `r', 
         and uses as backedge operands of gates (these are never counted) *)
      res := instr;
      WHILE (res # NIL) DO
        use := res. useList;
        WHILE (use # NIL) DO
          IF (use. instr # instr) & (use. instr. region = r) & 
             ~BackedgeOpnd (use) & 
             ((res # instr) OR ~MergeUse (instr, use. instr)) THEN
            DEC (use. instr. marker);
            IF (use. instr. marker = 0) THEN
              next := AddToReady (use. instr)
            END
          END;
          use := use. nextUse
        END;
        res := res. nextResult
      END
    END ScheduleInstr;

  PROCEDURE DelayedRegion (r: D.Region): BOOLEAN;
  (* TRUE iff `r' is a region that is always scheduled together with a merge,
     and never on its own.  *)
    VAR
      use, opnd: D.Opnd;
    BEGIN
      use := r. useList;
      WHILE (use # NIL) DO
        IF (use. instr. region = r. region) & 
           (use. instr IS D.Merge) & 
           (use. instr. opcode # Opc.mergeLoop) THEN
          opnd := use. instr. opndList;
          WHILE (opnd # NIL) & (opnd. location # auxLocation) DO
            IF r. Dominates (opnd. arg(D.Region)) THEN
              RETURN TRUE
            END;
            opnd := opnd. nextOpnd
          END
        END;
        use := use. nextUse
      END;
      RETURN FALSE
    END DelayedRegion;
  
  BEGIN
    (* schedule the contents of all nested regions *)
    nested := r. regionList;
    WHILE (nested # NIL) DO
      Schedule (nested);
      IF DelayedRegion (nested) THEN
        INCL (nested. flags, Class.instrDelayedRegion)
      END;
      nested := nested. nextRegion
    END;
    
    (* note: thanks to the preprocessing done by RegionDependencies we only
       have to consider dependencies between instructions of region `r'; all
       other data dependencies can be ignored *)
    
    (* initialize sorting algorithm; afterwards field `marker' holds the number
       of unresolved local dependencies for every instruction *)
    unscheduled := 0;
    instr := r. instrList;
    WHILE (instr # NIL) DO
      instr. marker := 0;
      skipLast := (instr. opcode = Opc.gate) &
                  (instr. opndList. arg(D.Merge). opcode = Opc.mergeLoop);
      opnd := instr. opndList;
      WHILE (opnd # NIL) DO
        IF (opnd. arg IS D.Result) & 
           (opnd. arg(D.Result). instr # instr) &
           (opnd. arg(D.Result). instr. region = instr. region) &
           ~(skipLast & (opnd. nextOpnd = NIL)) THEN
          INC (instr. marker)
        END;
        opnd := opnd. nextOpnd
      END;
      INC (unscheduled);
      instr := instr. nextInstr
    END;
    
    (* initialize selection algorithm for the current region `r' *)
    InitSelection (r);
    
    (* create initial ready list *)
    instr := r. instrList;
    WHILE (instr # NIL) DO
      IF (instr. marker = 0) & 
         ((instr. opcode = Opc.mergeLoop) OR ~(instr IS D.Merge)) THEN
        (* since calling AddToReady for guards/merges can effect the dependence
           count of their merge it has to be done after the count for all 
           instructions has been completed; if a merge is schedulable at the
           very start of its region, it'll be added implicitly to the ready set
           by calling AddToReady for its arguments *)
        instr := AddToReady (instr)
      ELSE
        instr := instr. nextInstr;
      END
    END;
    
    (* schedule local instructions and regions; any instruction with 
       `marker=0' is schedulable; `unscheduled' keeps track of the number of
       not yet scheduled instructions in the current region *)
    scheduled := NIL;
    WHILE (ready. instrList # NIL) DO
      (* select an instruction from the ready set and schedule it *)
      instr := Select (ready);
      ScheduleInstr (instr)
    END;

(*DEBUG: if the scheduler hangs comment out the lines marked with DEBUG in 
  procedure `InitSelection' and uncomment the IF statement below; you must also
  add Out and WriteGSA to the module's import list *)
<* IF Schedule_DEBUG THEN *>
    IF (unscheduled # 0) THEN
      Out.String ("backend/ansi-c/Schedule.Mod: Cyclic instruction dependence");
      Out.Ln;
      (* mark all unscheduled instructions, then write GSA code *)
      instr := r. instrList;
      WHILE (instr # NIL) DO
        IF (instr. marker # markerScheduled) THEN
          Out.String ("  ");
          WriteGSA.WrOpcode (instr. opcode);
          instr. pos := WriteGSA.mark;
          Out.String ("  ");
          Out.LongInt (instr. marker, 0);
          Out.Ln
        END;
        instr := instr. nextInstr
      END;
      WriteGSA.Body (r. Greg())
    END;
<* END *>

<* PUSH; Assertions := TRUE *> (* paranioa setting, always check for cycles *)
    ASSERT (unscheduled = 0, 1);
<* POP *>
    (* whenever this assertion triggers the ready set is empty but unscheduled 
       instructions remain; this is either caused by a buggy scheduler 
       (hopefully not), or by a cyclic instruction dependence in the GSA code
       (more likely); follow the instructions in the comment above marked with 
       DEBUG to get more useful information about the problem *)
  END Schedule;

PROCEDURE Cleanup (r: D.Region);
(* Removes all auxiliary operands.  *)
  VAR
    instr: D.Instruction;
    opnd, next: D.Opnd;
  BEGIN
    instr := r. instrList;
    WHILE (instr # NIL) DO
      opnd := instr. opndList;
      WHILE (opnd # NIL) DO
        next := opnd. nextOpnd;
        IF (opnd. location = auxLocation) THEN
          opnd. DeleteOperand()
        END;
        opnd := next
      END;
      IF (instr IS D.Region) THEN
        Cleanup (instr(D.Region))
      END;
      instr := instr. nextInstr
    END
  END Cleanup;

PROCEDURE Region* (greg: D.GlobalRegion);
  VAR
    instr: D.Instruction;
  
  PROCEDURE PassStoreToExit (exit: D.Instruction; greg: D.GlobalRegion);
  (* Make exit depend on the final value of $store.  Otherwise it might happen
     that exit is scheduled before an assignment to $store, meaning that a
     procedure is left without executing the assignment.  *)
    VAR
      instr: D.Instruction;
    BEGIN
      IF (exit # NIL) THEN
        instr := greg. instrList;
        WHILE (instr # NIL) & (instr. opcode # Opc.deleteStore) DO
          instr := instr. nextInstr
        END;
        IF (instr # NIL) THEN
          exit. UniqueOperand (instr, auxLocation)
        END
      END
    END PassStoreToExit;
  
  BEGIN
    (* turn anti-dependencies into data-dependencies *)
    greg. NumberDominanceTree();
    GuardCond.Init (greg);  (* sets info fields of instructions to NIL *)
    DataDependencies (greg, greg);

    (* add corresponding gate operands to regions that are left through a merge
       to make sure that the values have been computed when the region is 
       scheduled *)
    BranchDependencies (greg);
    PassStoreToExit (greg. ExitInstr(), greg);
    
    (* make hidden dependencies between regions explicit *)
    RegionDependencies (greg);

    (* do topological sort *)
    Schedule (greg);
    infoList := NIL;
    
    (* move enter to the very start and exit to the very end of its respective
       region *)
    instr := greg. EnterInstr();
    instr. MoveBehind (NIL);
    instr := greg. ExitInstr();
    IF (instr # NIL) THEN
      instr. MoveInFront (NIL)
    END;

    (* cleanup: remove all additional operands *)
    Cleanup (greg);
  END Region;

PROCEDURE ExecutedBefore* (a, b: D.Instruction): BOOLEAN;
(* Returns TRUE iff every time that `b' is evaluated `a' has been evaluated
   beforehand.  Or in other words: the instruction `a' is part of every path
   from the greg's beginning to `b'.  
   Note that is predicate can only be used after Schedule.Region has been 
   run.  *)
  BEGIN
    IF (a = b) THEN  (* both parameters refer to the same instruction *)
      RETURN FALSE
    ELSE
      WHILE (b # NIL) & (b. region # a. region) DO
        b := b. region
      END;
      IF (b # NIL) THEN
        WHILE (a # NIL) & (a # b) DO
          a := a. nextInstr
        END
      END;
      RETURN (b # NIL) & (a # NIL)
    END
  END ExecutedBefore;

BEGIN
  NEW (auxObj);
  D.InitObject (auxObj, "", D.objRestParam, D.undefPos);
  auxLocation := D.CreateSymLocation (auxObj, D.symLocObject);
  NEW (ready);
  D.InitRegion (ready, D.undefPos);
  infoList := NIL
END Schedule.
