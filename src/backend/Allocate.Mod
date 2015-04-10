(* 	$Id: Allocate.Mod,v 2.34 1999/06/03 12:10:42 acken Exp $	 *)
MODULE Allocate;
(*  Adds location attributes to GSA code.
    Copyright (C) 1996-1999  Michael van Acken

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
  D := Data, Opc := Opcode, Sym := SymbolTable, Class := Classify, Schedule,
  StdTypes, SF := SystemFlags, GenConst, Strings, IntStr, Out, TextRider;

(*
Note 1:
This is an implementation of a hierarchical graph allocator, assigning GSA
values to a (hopefully small) number of C variables.  Compared to an allocator
for a cpu it's somewhat simpler since it works with an unlimited number of
registers (variables) and therefore doesn't do any register spilling.

Note 2:
This module assumes that every instruction has at most one result that is
stored in a register (variable).  This result is always represented by the
instruction object itself.

Note 3:
The handling of gates differs from other instructions.  This holds for the gate
arguments as well as for the gate itself. The live range of a gate always
begins at the start of its region, and not at the place the instruction happens
to occupy in the merge.  On the other hand, all gate arguments that are
calculated outside the merge and are not used in any other way inside the
merge, do not have any live range in the merge region.  In this they differ
from all the other global live ranges.  From the outside, i.e. when integrating
the merge into the interference graph of another region, they have to be
treated as arguments of the merge, although only the part of the values
corresponding to the selected path into the merge are active at the same time.

Note 4:
The integration of a region's interference information into that of its
enclosing region is slightly tricky.  There are 4 kinds of global live ranges
plus the local ones (see sketch below).  Local live ranges [1] begin and end in
the region.  This means that they are calculated inside the region and all uses
are part of the region (i.e. the region itself or one of its nested regions).
Global live ranges are either calculated outside the region and used within
[2], or calculated inside the region and used outside [3].  Note that live
ranges that extend across the region, but are not used in it, take to effect
when building the interference graph of this region.  A special case of [2] are
live ranges that start outside the region, are used inside, and are also used
further down the path of control beyond the current region [4].  They are alive
across the whole region and cannot share a location with another local or
global region.  Their value is passed into the region in a given location and
it cannot be changed throughout the region.
  Global live ranges [5] that only serve as arguments to gates are ignored
inside the region (i.e. they do not interfere with local or global live
ranges), but they have to be considered when building the interference graph of
the enclosing region.
  Note that after coloring [2] and [3] may share locations with local live
ranges.  If this happens, the live range of the global value is basically
extended to cover all local live ranges with the same location.  These extended
live ranges may cause additional interference between [2] and [3], and the
interference matrix for the global ranges that is passed to the enclosing 
region has to be updated accordingly.

          global lr (in)
              v      v                            v
        --+   |      - global lr (gate arg)       | global lr (in)
          #   |        [5]                        | live across region
          #   |                                   |
          #   |                                   |
   extent #   |      *                            |
     of   #   |      | local lr                   |
   region #   *      |                            * (local use)
          #  [2]     |                            |
          #          |     *                      |
          #          *     | global lr (out)      |
          #         [1]    |                      |
          #                |                      |
        --+                |                      |
                           v                      v
                          [3]                    [4]
             
*)

TYPE
  Location* = POINTER TO LocationDesc;
  LocationDesc = RECORD
    (D.LocationDesc)
    value-: D.String;
    old-: D.SymLocation;
    (* when replacing a `SymLocation' by a C location, this field keeps the
       original location; this is used to reconstruct the orginal form of the
       enter and exit instructions (required by the front-end) *)
    outerLocation: Location;
    (* if this location represents a single virtual register of a nested
       region, then this field refers to the location that is assigned to this
       register in the enclosing region *)
    used: BOOLEAN;
    (* when colorizing the graph in `ColorGraph' this field is set to TRUE if
       a neighbour of the given node is placed at this location *)
    gid: LONGINT;
  END;

TYPE
  BitMatrix = POINTER TO ARRAY OF ARRAY OF SET;
  BitVector = POINTER TO ARRAY OF SET;
  LongintVector = POINTER TO ARRAY OF LONGINT;
  ResultVector = POINTER TO ARRAY OF D.Info;
  RangeInfo = RECORD
    rows, currRows: LONGINT;
    (* length of the vectors and the first dimension of field `m'; `rows' is
       the number of bits resp. lines allocated, `currRows' the number actually
       in use; `rows' is equal to or larger than `currRows' *)
    cols, currCols: LONGINT;
    (* number of elements of type SET allocated in `m' and `v'; if holds:
       `cols = (rows+bitsPerSet-1) DIV bitsPerSet'; `cols' is the number of
       elements allocated, `currCols' the number actually in use; `cols' is
       equal to or larger than `currCols' *)
    m: BitMatrix;
    (* this matrix holds the interference matrix of live ranges in the current
       region that apply to the given register set; see BuildInterferenceGraphs
       resp. ColorGraph *)
    v: BitVector;
    (* this vector describes in BuildInterferenceGraphs the set of currently
       live ranges *)
    d: LongintVector;
    (* holds the current degree of the nodes of the interference graph during
       graph coloring; see ColorGraphs *)
    s: LongintVector;
    (* serves as stack during ColorGraphs; an element holds the index of a live
       range *)
    ds: LongintVector;
    (* maps indices of array `d' onto array `s', i.e. s[ds[i]]=i resp. 
       ds[s[i]]=i; used in ColorGraph to keep the complexity of the heap sort
       at O(n*log(n)) *)
    res: ResultVector
    (* this array maps a live range index onto the result that starts the
       range; it holds: `res[i](D.Result). marker = i'; for live ranges that
       represent local register usage of a nested region an instance of
       `Location' is used instead *)
  END;

  LocationVector = POINTER TO ARRAY OF Location;

CONST
  noMark = -1;
  (* this value is stored in `Result.marker' for results that haven't been
     assigned their id yet by the preprocessing step in procedure Region *)
     
  registers = {Class.instrInt..Class.instrLongReal};
  (* this set holds the flags that mark the use of one of the register classes;
     if for an instruction `i.flags*registers # {}' holds, a register has to be
     allocated to hold the result of the instruction *)
  regOff = Class.instrInt;
  (* used to map elements of a `registers' set onto array indices *)
  registerFiles = Class.instrLongReal-Class.instrInt+1;
  (* number of distinct register files in use *)
  
  bitsPerSet = SIZE (SET)*8;
  (* number of bits in a SET *)

TYPE
  RegionSummary = POINTER TO RegionSummaryDesc;
  LiveRangeList = POINTER TO LiveRangeListDesc;

  RegFileSummary = RECORD
    globalCount: LONGINT;
    (* number of global live ranges (originating or ending in the region); in 
       other words: the number of elements in the list `globals' *)
    globals: LiveRangeList;
    (* list of global live ranges *)
    gateArgs: LiveRangeList;
    (* list of nonlocal results appearing as arguments to this region's gates;
       unlike the elements in `globals' they do not represent a live range of
       the current region *)
    localCount: LONGINT;
    (* number of registers allocated by this region in the respective register
       file to hold strictly local live ranges; global live ranges are not
       included *)
    localStart: LONGINT;
    (* holds the index that is assigned to the first local register in the
       enclosing region *)
    gi: BitMatrix;
    (* interference matrix for global live ranges *)
    locations: LocationVector;
    (* list of locations assigned to the various (local or global) live ranges
       in the region; the first `globalCount' elements refer to the
       locations of global live ranges, of which each has (preliminary) a
       distinct place; following them is the list of strictly local locations;
       note:
       results starting a global live range have NIL as location after 
       ColorGraph has been run on the region, but local life ranges may share 
       the same location and _their_ defining result has their respective 
       location attribute set; the `outer' field is the location that is 
       assigned by the enclosing region; both have to refer to the same 
       register in the end *)
    lrCount: LONGINT;
    (* number of live ranges; used by BuildInterferenceGraphs, should not be
       used in any of the following phases *)
  END;
  RegionSummaryDesc = RECORD
  (* this record contains the information that is passed from every region to
     its respective enclosing region while doing a bottom-up coloring of the
     GSA tree *)
    (D.InfoDesc)
    rf: ARRAY registerFiles OF RegFileSummary
  END;
  LiveRangeListDesc = RECORD
    next: LiveRangeList;
    (* refers to next element in list *)
    result: D.Instruction;
    (* a live range desribed by the generating result; a global live range is
       either defined outside but used inside the given region, or vice versa*)
  END;

VAR
  rangeInfo: ARRAY registerFiles OF RangeInfo;
  locCount: LONGINT;
  locVector: LocationVector;
  liveStack: BitVector;(* holds temporary live vectors during IntegrateMerge *)
  topStack: LONGINT;   (* first free element in `liveStack' *)
  undefResult: D.Result;
  copyMarker: D.Info;
  
VAR  (* debug *)
  allocCounter: ARRAY 256 OF LONGINT;


PROCEDURE NewLoc* (str: ARRAY OF CHAR): Location;
(* Creates a new instance of `Location' and intializes it.  If `str' is the
   empty string, the `value' attribute is set to NIL, otherwise to a copy of
   `str'.  *)
  VAR
    l: Location;
  BEGIN
    NEW (l);
    l. old := NIL;
    l. outerLocation := NIL;
    l. used := FALSE;
    l. gid := noMark;
    IF (str[0] # 0X) THEN
      NEW (l. value, Strings.Length (str)+1);
      COPY (str, l. value^)
    ELSE
      l. value := NIL
    END;
    RETURN l
  END NewLoc;



(* first define some auxiliary functions to handle access of C variables; ugly
   stuff, agreed; translating into a high level language can have its
   disadvantages *)

PROCEDURE GetLocation* (u: D.Node): D.SymLocation;
  VAR
    l: D.Location;
  BEGIN
    IF (u = NIL) THEN
      RETURN NIL
    ELSE
      WITH u: D.Result DO
        l := u. location
      | u: D.Opnd DO
        l := u. location
      END;
      IF (l = NIL) THEN
        RETURN NIL
      ELSE
        WITH l: D.SymLocation DO
          RETURN l
        | l: Location DO
          RETURN l. old
        END
      END
    END
  END GetLocation;

PROCEDURE FindResult* (instr: D.Instruction;
                       var: D.Addressable; attrib: INTEGER): D.Result;
(* Locates result of given symbolic location.  *)
  VAR
    res: D.Result;
    loc: D.SymLocation;
  BEGIN
    res := instr. nextResult;
    loc := GetLocation (res);
    WHILE (res # NIL) & ((loc. var # var) OR (loc. attrib # attrib)) DO
      res := res. nextResult;
      loc := GetLocation (res)
    END;
    RETURN res
  END FindResult;

PROCEDURE FindOperand* (instr: D.Instruction;
                        var: D.Addressable; attrib: INTEGER): D.Opnd;
(* Locates operand of given symbolic location.  *)
  VAR
    opnd: D.Opnd;
    loc: D.SymLocation;
  BEGIN
    opnd := instr. opndList;
    loc := GetLocation (opnd);
    WHILE (opnd # NIL) & 
          ((loc = NIL) OR (loc. var # var) OR (loc. attrib # attrib)) DO
      opnd := opnd. nextOpnd;
      loc := GetLocation (opnd)
    END;
    RETURN opnd
  END FindOperand;


PROCEDURE PtrValue* (t: D.Struct): BOOLEAN;
  BEGIN
    RETURN Sym.TypeInGroup (t, D.grpPtr) OR (t. form = D.strProc)
  END PtrValue;

PROCEDURE ConcatLoc (str1, str2, str3: ARRAY OF CHAR): Location;
  VAR
    l: Location;
  BEGIN
    NEW (l);
    NEW (l. value, Strings.Length (str1)+Strings.Length (str2)+
                   Strings.Length (str3)+1);
    COPY (str1, l. value^);
    Strings.Append (str2, l. value^);
    Strings.Append (str3, l. value^);
    l. old := NIL;
    RETURN l
  END ConcatLoc;

PROCEDURE AccessNonlocal* (greg: D.GlobalRegion; var: D.Object;
                           prefix: ARRAY OF CHAR): Location;
  VAR
    name, deref: ARRAY 1024 OF CHAR;
    exit: D.Instruction;
  BEGIN
    IF (prefix = "") & PtrValue (var. type) THEN
      StdTypes.BasicTypes (D.strAddress, name);
      Strings.Insert ("(", 0, name);
      Strings.Append (")", name)
    ELSE
      name := ""
    END;

    COPY (name, deref);
    exit := greg. ExitInstr();
    IF (var. level > Sym.globalLevel) &
       (StdTypes.PassPerReference (var, TRUE) OR
        (FindResult (greg. EnterInstr(), var, D.symLocAddress) # NIL) OR
        (exit # NIL) & (FindOperand (exit, var, D.symLocObject) # NIL) OR
        (exit # NIL) & (FindOperand (exit, Sym.mem, D.symLocObject) # NIL)) &
       ~Sym.TypeInGroup (var. type, D.grpArray) THEN
      Strings.Append ("*", deref)
    END;

    IF (var. level = Sym.globalLevel) THEN
      RETURN ConcatLoc (prefix, deref, var. beInfo(SF.Info). name^)
    ELSE
      COPY (prefix, name);
      Strings.Append (deref, name);
      Strings.Append (var. localTo(D.Object). beInfo(SF.Info). name^, name);
      RETURN ConcatLoc (name, "_", var. beInfo(SF.Info). name^)
    END
  END AccessNonlocal;

PROCEDURE GetAddressValue* (greg: D.GlobalRegion; arg: D.Usable; castToInt: BOOLEAN): Location;
(* Build a C expression that holds the address of the object designated by
   `arg' and put it into a `Location' object.  *)
  VAR
    adrCast, name: ARRAY 64 OF CHAR;
  BEGIN
    IF castToInt THEN
      StdTypes.BasicTypes (D.strAddress, adrCast);
      Strings.Insert ("(", 0, adrCast);
      Strings.Append (")", adrCast)
    ELSE
      adrCast := ""
    END;

    WITH arg: D.Object DO
      (* only add the address prefix if we aren't getting the address of a
         fixed size or an open array, or of a value parameter that has 
         no local copy *)
      IF ~Sym.TypeInGroup (arg. type, D.grpArray) &
         ((arg. mode # D.objVar) OR ~(D.objIsParameter IN arg. flags) OR
          ~StdTypes.PassPerReference (arg, FALSE) OR
          (StdTypes.objLocalCopy IN arg. beFlags)) THEN
        Strings.Append ("&", adrCast)
      END;

      IF (greg. bodyOf # arg. localTo) THEN
        RETURN AccessNonlocal (greg, arg, adrCast)
      ELSE
        IF ~Sym.TypeInGroup (arg. type, D.grpArray) &
           (arg. mode = D.objVarPar) &
           StdTypes.PassPerReference (arg, TRUE) THEN
          Strings.Append ("*", adrCast)
        ELSIF (arg. mode = D.objVar) THEN
          INCL (arg. beFlags, StdTypes.objUsedLocalVar)
        END;
        RETURN ConcatLoc (adrCast, "", arg. beInfo(SF.Info). name^)
      END
    | arg: D.Struct DO
      (* the "address" of a type is the address of its type descriptor;
         here holds: arg.form = D.strRecord *)
      COPY (arg. beInfo(SF.Info). name^, name);
      Strings.Append ("_td.td", name);
      RETURN ConcatLoc ("", "&", name)
    | arg: D.Const DO
      (* string constants are collected into a single block of named
         declarations *)
      GenConst.InsertString (arg, name);
      RETURN ConcatLoc (adrCast, "", name)
    END
  END GetAddressValue;

PROCEDURE TransformLocation* (greg: D.GlobalRegion; loc: D.SymLocation): D.Location;
  VAR
    str: ARRAY 1024 OF CHAR;
    suffix, prefix: ARRAY 512 OF CHAR;
    obj: D.Object;
    info: SF.Info;
    l: Location;

  PROCEDURE NonlocalRef (greg: D.GlobalRegion; obj: D.Object): BOOLEAN;
    BEGIN
      RETURN (obj. level > Sym.globalLevel) & (obj. localTo # greg. bodyOf)
    END NonlocalRef;

  PROCEDURE NonlocalPassPerRef (greg: D.GlobalRegion; obj: D.Object): BOOLEAN;
  (* Returns TRUE iff `obj' is a nonlocal variable that is passed per reference
     to `greg'.  *)
    BEGIN
      IF NonlocalRef (greg, obj) THEN
        IF StdTypes.PassPerReference (obj, FALSE) THEN
          RETURN TRUE
        ELSE
          RETURN
            (FindResult (greg. EnterInstr(), obj, D.symLocAddress) # NIL) OR
            (FindOperand (greg. ExitInstr(), obj, D.symLocObject) # NIL) OR
            (FindOperand (greg. ExitInstr(), Sym.mem, D.symLocObject) # NIL)
        END
      ELSE
        RETURN FALSE
      END
    END NonlocalPassPerRef;

  BEGIN
    IF (loc. var IS D.Object) &
       ((loc. var(D.Object). name^ = "$mem") OR
        (loc. var(D.Object). name^ = "$store")) OR
       (loc. var IS D.Struct) THEN
      RETURN loc
    ELSE
      suffix := ""; prefix := "";
      CASE loc. attrib OF
      | D.symLocTypeTag:  (* type tag of variable record parameter *)
        suffix := "__tag"
      | D.symLocAddress:  (* address of parameter passed per reference *)
        StdTypes.BasicTypes (D.strAddress, prefix);
        Strings.Insert ("(", 0, prefix);
        Strings.Append (")", prefix);
        IF (loc. var IS D.Object) & 
           (loc. var(D.Object). level = Sym.globalLevel) &
           (loc. var(D.Object). type. form # D.strArray) THEN
          (* avoid address operator in front of array variable; some C 
             compilers emit a warning for this nonsense operation *)
          Strings.Append ("&", prefix)
        END
      | D.symLocObject:   (* parameter value of arbitrary type *)
        IF (StdTypes.PassPerReference (loc. var(D.Object), TRUE) OR
            NonlocalPassPerRef (greg, loc. var(D.Object))) &
           ~Sym.TypeInGroup (loc. var(D.Object). type, D.grpArray) THEN
          prefix := "*"
        END
      ELSE                (* length of open array parameter *)
        IntStr.IntToStr (loc. attrib, suffix);
        Strings.Append ("d", suffix);
        Strings.Insert ("_", 0, suffix)
      END;

      obj := loc. var(D.Object);
      info := obj. beInfo(SF.Info);
      IF (loc. var(D.Object). type. form = D.strChar8) & 
         ~(StdTypes.PassPerReference (loc. var(D.Object), TRUE) OR
            NonlocalPassPerRef (greg, loc. var(D.Object))) THEN
        (* cast unsigned character type onto signed integer; this avoids 
           problems due to comparing signed and unsiged values *)
        StdTypes.BasicTypes (D.strLongInt, str);
        Strings.Insert ("(", 0, str);
        Strings.Append (")", str)
      ELSIF (loc. attrib < D.symLocLength0) &
         PtrValue (loc. var(D.Object). type) THEN
        (* convert pointer values to integer value *)
        StdTypes.BasicTypes (D.strAddress, str);
        Strings.Insert ("(", 0, str);
        Strings.Append (")", str)
      ELSE
        str := ""
      END;
      Strings.Append (prefix, str);
      IF NonlocalRef (greg, obj) THEN
        Strings.Append (obj. localTo(D.Object). beInfo(SF.Info). name^, str);
        Strings.Append ("_", str)
      END;
      Strings.Append (info. name^, str);
      Strings.Append (suffix, str);

      l := NewLoc (str);
      l. old := loc;
      RETURN l
    END
  END TransformLocation;


PROCEDURE ResolveVarConflicts (greg: D.GlobalRegion);
(* Looks for possible conflicts between live ranges living in local scalar 
   variables of `greg' and inserts copy instructions to fix the problem.  Such
   conflicts can happen whenever a procedure call modifies a local scalar 
   variable of the caller, eiter through a variable parameter or because
   the callee is a nested procedure writing to a nonlocal variable.  Because of
   unlucky scheduling or, more often, through lost copy instructions, one call
   clobbers the memory of a local variable that is holding a value that's
   actually used later on.  The most simple example is this:
     ReadChar(a); b := a; ReadChar(a); x := ORD(a)+ORD(b)
   The GSA code from the frontend will drop the intermediate assignment and do
   both calls in a row; the second call will clobber the old value of `a', 
   implicitly using the value of `a' for the variable `b'; in the end `x' will
   hold `2*ORD(a)'.  
   This procedure notices that the memory of `a' is used by two overlapping
   live ranges and inserts a copy that will rescue the value of the first
   live range before the second call gets the chance to overwrite it.
   Note that the chance of such conflicts is quite small: at the time of 
   writing this procedure finds only 26 potential for the whole oo2c source 
   code (ca. 1.8MB of code); most (all?) of those will be wrong, but it isn't
   worth the effort to try harder.
   pre: Data.NumberDominanceTree still valid, scheduling has been done *)
  TYPE
    InfoArray = POINTER TO RECORD 
      (D.InfoDesc)
      list: POINTER TO ARRAY OF RECORD 
        reads: D.Result;
        writes: D.Usable
      END
    END;
  VAR
    counter, icounter: LONGINT;
    conflict: BOOLEAN;
    
  PROCEDURE MarkObjects (obj: D.Object);
    VAR
      marker: LONGINT;
    BEGIN
      IF (obj # NIL) THEN
        MarkObjects (obj. leftObj);
        IF (obj. mode = D.objVar) & 
           ~Sym.TypeInGroup (obj. type, D.grpStructured) THEN
          marker := counter;
          INC (counter)
        ELSE
          marker := -1
        END;
        IF (D.objIsParameter IN obj. flags) THEN
          (* mark the correct copy of the the parameter object, the one that
             is part of the procedure's scope won't appear in locations *)
          obj. data(D.Object). marker := marker
        ELSE
          obj. marker := marker
        END;
        MarkObjects (obj. rightObj)
      END
    END MarkObjects;
  
  PROCEDURE MarkInstructions (r: D.Region);
    VAR
      instr: D.Instruction;
    BEGIN
      instr := r. instrList;
      WHILE (instr # NIL) DO
        instr. marker := icounter;
        INC (icounter);
        IF (instr IS D.Region) THEN
          MarkInstructions (instr(D.Region))
        END;
        instr := instr. nextInstr
      END
    END MarkInstructions;
  
  PROCEDURE NewInfo (): InfoArray;
    VAR
      ia: InfoArray;
      i: LONGINT;
    BEGIN
      NEW (ia);
      NEW (ia. list, counter);
      FOR i := 0 TO counter-1 DO
        ia. list[i]. reads := NIL;
        ia. list[i]. writes := NIL
      END;
      RETURN ia
    END NewInfo;
  
  PROCEDURE CopyInfo (ia: InfoArray): InfoArray;
    VAR
      ib: InfoArray;
      i: LONGINT;
    BEGIN
      ib := NewInfo();
      FOR i := 0 TO counter-1 DO
        ib. list[i]. reads := ia. list[i]. reads;
        ib. list[i]. writes := ia. list[i]. writes
      END;
      RETURN ib
    END CopyInfo;
  
  PROCEDURE ScanRegions (r: D.Region): BOOLEAN;
  (* Scan has to be repeated iff result is TRUE.  *)
    VAR
      obj: D.Object;
      ia: InfoArray;
      r0: D.Region;
      res: D.Result;
      opnd: D.Opnd;
      instr, prevInstr: D.Instruction;
      i: LONGINT;
      merge: D.Merge;
    
    PROCEDURE ScalarLocalVar (loc: D.Location; VAR obj: D.Object): BOOLEAN;
    (* Returns TRUE iff `loc' refers to a local scalar variable of the 
       current procedure or module body.  *)
      BEGIN
        IF (loc # NIL) & (loc(D.SymLocation). var IS D.Object) THEN
          obj := loc(D.SymLocation). var(D.Object);
          RETURN (obj. localTo = greg. bodyOf) & (obj. marker >= 0)
        ELSE
          RETURN FALSE
        END
      END ScalarLocalVar;
    
    PROCEDURE Conflict (res0, res1: D.Result);
      PROCEDURE Copy (res: D.Result);
        VAR
          instr: D.Instruction;
        BEGIN
          instr := res. instr. region. CreateInstruction (Opc.copy, res. type, res. instr. pos);
          (* assign copy instruction to a register set; without this the
             allocator would ignore it since instruction classification has
             been done already *)
          INCL (instr. flags, Class.RegClass (res. type));
          instr. MoveBehind (res. instr);
          res. ReplaceUses (instr);
          instr. Operand (res);
          instr. info := copyMarker
        END Copy;
      
      BEGIN
        (* make sure that we aren't trying to create a copy instruction to
           remove a conflict triggered by a previously inserted copy 
           instruction: sure way to get an endless loop *)
        IF (res1 # NIL) & (res1. useList. nextUse = NIL) &
           (res1. useList. instr. info = copyMarker) THEN
          res1 := NIL
        END;
        IF (res0 # NIL) & (res0. useList. nextUse = NIL) &
           (res0. useList. instr. info = copyMarker) THEN
          res0 := res1
        END;
        
        IF (res1 # NIL) THEN
          (* guess which instruction is executed before the other and insert
             a copy for it; it doesn't matter much if the guess is wrong, the
             second scan would fix it *)
          IF (res0. instr. marker < res1. instr. marker) THEN
            Copy (res0)
          ELSE
            Copy (res1)
          END
        ELSE
          Copy (res0)
        END
      END Conflict;
    
    PROCEDURE WriteConflict (ia: InfoArray; u: D.Usable; 
                             marker: LONGINT): BOOLEAN;
      BEGIN
        IF (ia. list[marker]. writes = NIL) THEN
          ia. list[marker]. writes := u
        END;
        IF (ia. list[marker]. reads = u) & (u # D.constUndef) THEN
          ia. list[marker]. reads := NIL
        ELSIF (ia. list[marker]. reads # NIL) THEN
          Conflict (ia. list[marker]. reads, NIL);
          RETURN TRUE
        END;
        RETURN FALSE
      END WriteConflict;
    
    PROCEDURE ReadConflict (ia: InfoArray; res: D.Result; 
                            marker: LONGINT): BOOLEAN;
      BEGIN
        IF (ia. list[marker]. reads = NIL) THEN
          ia. list[marker]. reads := res
        ELSIF (ia. list[marker]. reads # res) THEN
          Conflict (res, ia. list[marker]. reads);
          RETURN TRUE
        END;
        RETURN FALSE
      END ReadConflict;
    
    PROCEDURE HandleRegion (ia: InfoArray; region: D.Region): BOOLEAN;
    (* Given all reads/writes from/to local variables after `region', calculate
       the read/writes in front of the region and put result into `ia'.  
       Returns  TRUE if a conflict was detected.  *)
      VAR
        nia: InfoArray;
        i: LONGINT;
      BEGIN
        nia := region. info(InfoArray);
        FOR i := 0 TO counter-1 DO
          IF (nia. list[i]. writes # NIL) &
             WriteConflict (ia, nia. list[i]. writes, i) THEN
            RETURN TRUE
          END
        END;
        FOR i := 0 TO counter-1 DO
          IF (nia. list[i]. reads # NIL) &
             ReadConflict (ia, nia. list[i]. reads, i) THEN
            RETURN TRUE
          END
        END;
        RETURN FALSE
      END HandleRegion;
    
    PROCEDURE ScanGates (ia: InfoArray; merge: D.Merge; opn: INTEGER): BOOLEAN;
      VAR
        use, opnd: D.Opnd;
      BEGIN
        use := merge. useList;
        WHILE (use # NIL) DO
          IF (use. instr. opcode = Opc.gate) & 
             (use = use. instr. opndList) THEN
            opnd := use. instr. NthOperand (opn);
            IF (opnd. arg IS D.Result) &
               ScalarLocalVar (opnd. arg(D.Result). location, obj) &
               ReadConflict (ia, opnd. arg(D.Result), obj. marker) THEN
              RETURN TRUE
            END            
          END;
          use := use. nextUse
        END;
        RETURN FALSE
      END ScanGates;
    
    PROCEDURE SummarizeMerge (merge: D.Merge): D.Instruction;
    (* Scan all possible paths into the `merge' region.  Detect conflicts and 
       summarize the read/write patterns of all paths into the object 
       `merge.info'.  Return `merge' itself if a conflict is detected, and the
       first instruction before the whole merge block otherwise.  *)
      VAR
        prev, prev0: D.Instruction;
        region: D.Region;
        mia, pia: InfoArray;
        opnd: D.Opnd;
        
      PROCEDURE Before (a, b: D.Instruction): BOOLEAN;
      (* TRUE iff `a' is scheduled before `b'.  
         pre: a.region=b.region *)
        BEGIN
          WHILE (a # NIL) & (a # b) DO
            a := a. prevInstr
          END;
          RETURN (a = NIL)
        END Before;
      
      BEGIN
        prev := NIL;
        opnd := merge. opndList;
        WHILE (opnd # NIL) DO
          region := opnd. arg(D.Region);
          WHILE (region. region # merge. region) DO
            region := region. region
          END;
          IF (region IS D.Merge) & (region. opcode # Opc.mergeLoop) THEN
            prev0 := SummarizeMerge (region(D.Merge));
            IF (prev0 = region) THEN
              RETURN merge (* conflict *)
            END
          ELSE
            prev0 := region. prevInstr
          END;
          IF (prev = NIL) OR Before (prev0, prev) THEN
            prev := prev0
          END;
          
          (* merge `region.info' with `merge.info' into `pia' *)
          pia := CopyInfo (merge.info(InfoArray));
          IF HandleRegion (pia, region) THEN
            RETURN merge (* conflict *)
          END;
          region. info := pia;
          
          opnd := opnd. nextOpnd
        END;
        
        (* merge `pia' into `mia'; fist handle all write information, then the
           read stuff *)
        mia := NewInfo();
        FOR i := 0 TO counter-1 DO
          IF (mia. list[i]. writes = NIL) THEN
            opnd := merge. opndList;
            WHILE (opnd # NIL) DO
              region := opnd. arg(D.Region);
              WHILE (region. region # merge. region) DO
                region := region. region
              END;
              pia := region. info(InfoArray);

              IF (pia. list[i]. writes # NIL) THEN
                IF (mia. list[i]. writes = NIL) THEN
                  mia. list[i]. writes := pia. list[i]. writes
                ELSIF (mia. list[i]. writes # pia. list[i]. writes) THEN
                  mia. list[i]. writes := D.constUndef
                END
              END;

              opnd := opnd. nextOpnd
            END
          END
        END;
        FOR i := 0 TO counter-1 DO
          opnd := merge. opndList;
          WHILE (opnd # NIL) DO
            region := opnd. arg(D.Region);
            WHILE (region. region # merge. region) DO
              region := region. region
            END;
            pia := region. info(InfoArray);
            
            IF (pia. list[i]. reads # NIL) &
               ReadConflict (mia, pia. list[i]. reads, i) THEN
              RETURN merge (* conflict *)
            END;
            
            opnd := opnd. nextOpnd
          END
        END;
        
        merge. info := mia;
        RETURN prev
      END SummarizeMerge;
    
    BEGIN
      (* scan nested regions; return to top-most caller if one region signals
         that the scan has to be repeated *)
      r0 := r. regionList;
      WHILE (r0 # NIL) DO
        IF ScanRegions (r0) THEN
          RETURN TRUE
        END;
        r0 := r0. nextRegion
      END;
      
      ia := NewInfo();
      IF (r. opcode = Opc.mergeLoop) THEN
        IF ScanGates (ia, r(D.Merge), 2) THEN
          RETURN TRUE
        END
      ELSE
        merge := r. RegionMerge();
        IF (merge # NIL) &
           ScanGates (ia, merge, merge. ArgumentIndex (r)+1) THEN
          RETURN TRUE
        END
      END;
      
      instr := r. instrTail;
      WHILE (instr # NIL) DO
        prevInstr := instr. prevInstr;
        
        IF (instr IS D.Region) THEN
          IF (instr IS D.Merge) & (instr. opcode # Opc.mergeLoop) THEN
            prevInstr := SummarizeMerge (instr(D.Merge));
            IF (prevInstr = instr) THEN  (* conflict *)
              RETURN TRUE
            END
          END;
          
          IF HandleRegion (ia, instr(D.Region)) THEN
            RETURN TRUE
          END
          
        ELSIF (instr. opcode # Opc.gate) THEN
          (* scan all results produced by the current instruction; if a result
             satisfies an argument further down, then remove it from the list
             of pending reads *)
          res := instr. nextResult;
          WHILE (res # NIL) DO
            IF ScalarLocalVar (res. location, obj) &
               WriteConflict (ia, res, obj. marker) THEN
              RETURN TRUE
            END;
            res := res. nextResult
          END;
          
          (* scan all values that forced into local variables by the current
             instruction *)
          opnd := instr. opndList;
          WHILE (opnd # NIL) DO
            IF ScalarLocalVar (opnd. location, obj) &
               ((instr. opcode # Opc.call) OR  (* ignore value arguments *)
                (opnd. GetFormalParam() = NIL)) &
               WriteConflict (ia, opnd. arg, obj. marker) THEN
              RETURN TRUE
            END;
            opnd := opnd. nextOpnd
          END;

          (* scan all values that are passed as arguments to the current 
             instruction  *)
          opnd := instr. opndList;
          WHILE (opnd # NIL) DO
            IF (opnd. arg IS D.Result) &
               ScalarLocalVar (opnd. arg(D.Result). location, obj) &
               ReadConflict (ia, opnd. arg(D.Result), obj. marker) THEN
              RETURN TRUE
            END;
            opnd := opnd. nextOpnd
          END
        END;
        
        instr := prevInstr
      END;
      
      (* integrate operands of the given region into current `ia'; this way
         the data stored in `r.info' will cover the whole region *)
      IF (r. opcode = Opc.mergeLoop) & ScanGates (ia, r(D.Merge), 1) THEN
        RETURN TRUE
      END;
      opnd := r. opndList;
      WHILE (opnd # NIL) DO
        IF (opnd. arg IS D.Result) &
           ScalarLocalVar (opnd. arg(D.Result). location, obj) &
           ReadConflict (ia, opnd. arg(D.Result), obj. marker) THEN
          RETURN TRUE
        END;
        opnd := opnd. nextOpnd
      END;
      r. info := ia;
      
      RETURN FALSE
    END ScanRegions;
  
  BEGIN
    counter := 0;
    MarkObjects (greg. bodyOf. localDecl);
    icounter := 0;
    MarkInstructions (greg);
    
    (* Scan greg for potential live range clashes.  If the algorithm inserts
       a copy abort scan and start from scratch.  This might look strange. 
       Well, it is ;-)  But chance of conflicts is quite small (for oo2c
       plus library modules, ca. 1.8MB of code, this procedure finds 26
       potential conflicts), therefore the number of repeated scans is
       negligible.  A changed algorithm that is guaranteed to do its job in
       one turn would probably take longer in terms of execution time.  *)
    REPEAT
      conflict := ScanRegions (greg)
    UNTIL ~conflict
  END ResolveVarConflicts;


(* the code for the hierarchical graph allocator begins here: *)

PROCEDURE TargetRegFile (instr: D.Instruction): SHORTINT;
(* Returns the id of the register file used by `instr' to store its result.
   Result is -1 if no result is produced.  *)
  VAR
    reg: SHORTINT;
  BEGIN
    IF (instr. flags * registers # {}) THEN
      (* instruction procedures exactly one result stored in a register *)
      reg := Class.instrInt;
      WHILE ~(reg IN instr. flags) DO
        INC (reg)
      END;
      RETURN reg-regOff
    ELSE
      RETURN -1
    END
  END TargetRegFile;

PROCEDURE BuildInterferenceGraphs (r: D.Region; summary: RegionSummary);
(* Builds the interference graphs for the region `r'.
   pre: All markers in `r' have been initialized to `noMark'; register
     allocation of all regions nested in `r' has been completed.
   post: The global variable `rangeInfo' holds the interference graphs for
     the various register files.  *)
  CONST
    gateArg = -2;
    (* value of `Result.marker' for results that only appear as arguments to 
       local gates *)
  VAR
    instr, liveRange: D.Instruction;
    region: D.Region;
    opnd, use: D.Opnd;
    arg: D.Usable;
    reg: SHORTINT;
    lr: LiveRangeList;
    i: LONGINT;
    ns: RegionSummary;
    regCount: ARRAY registerFiles OF LONGINT;

  PROCEDURE NonlocalUse (res: D.Result; region: D.Region): BOOLEAN;
  (* Returns TRUE iff `res' is used in a region that is not equal to `region'
     and isn't nested in `region'.  *)
    VAR
      use: D.Opnd;
    BEGIN
      use := res. useList;
      WHILE (use # NIL) DO
        IF ~region. Dominates (use. instr. region) THEN
          RETURN TRUE
        END;
        use := use. nextUse
      END;
      RETURN FALSE
    END NonlocalUse;

  PROCEDURE LiveAcrossRegion (instr: D.Instruction; r: D.Region): BOOLEAN;
  (* Returns TRUE if `instr' is used somewhere after `r', i.e. if the live 
     range of `instr' doesn't end in `r' but reaches beyond it.
     pre: ~D.Dominates (r, instr. region) *)
    VAR
      use: D.Opnd;
      useRegion: D.Region;
    
    PROCEDURE PathExists (from:D.Region; to: D.Instruction): BOOLEAN;
    (* Returns FALSE if it can be proven that control will never pass from 
       region `from' to instruction `to' (ignoring loops).
       pre: ~D.Dominates (from, to. region) *)
       
      PROCEDURE PlacedAfter (a, b: D.Instruction): BOOLEAN;
      (* Returns TRUE iff `a' is placed after `b' in the region's instruction 
         list.
         pre: a.region=b.region *)
        BEGIN
          WHILE (b # NIL) & (b # a) DO
            b := b. nextInstr
          END;
          RETURN (b = a)
        END PlacedAfter;
      
      BEGIN
        WHILE (from. region # to. region) DO
          IF from. region. Dominates (to. region) THEN
            to := to. region
          ELSE
            from := from. region
          END
        END;
        (* note: this is only a conservative approximation; there may be 
           situations where `to' is placed after `from' without an actual
           path of control towards `to', e.g. whenever the two represent
           different arguments of a given merge *)
        RETURN PlacedAfter (to, from)
      END PathExists;
    
    BEGIN
      use := instr. useList;
      WHILE (use # NIL) DO
        useRegion := use. instr. region;
        IF ~r. Dominates (useRegion) & 
           ((use. instr. opcode = Opc.gate) & (use. nextOpnd = NIL) &
             (use. instr. opndList. arg(D.Merge). opcode = Opc.mergeLoop) OR
            PathExists (r, use. instr)) THEN
          RETURN TRUE
        END;
        use := use. nextUse
      END;
      
      (* `r' or one of its enclosing regions is a loop to which `instr' is a
         global live range, then `instr' is live across `r' *)
      WHILE (r # NIL) DO
        IF (r. opcode = Opc.mergeLoop) & ~r. Dominates (instr. region) THEN
          RETURN TRUE
        END;
        r := r. region
      END;
      
      (* the live range of `instr' ends with the last use of it in `r' *)
      RETURN FALSE
    END LiveAcrossRegion;

  PROCEDURE AddToGlobal (r: D.Region; VAR rf: RegFileSummary; 
                         reg: SHORTINT; instr: D.Instruction);
  (* Adds `instr' to the list of global live ranges of the current region `r'.
     The index of `instr' is adjusted to get the first indices assigned in `r'
     to refer to global ranges.  *)
    VAR
      lr, l: LiveRangeList;

    PROCEDURE LocalGateArg (merge: D.Instruction; result: D.Result): BOOLEAN;
    (* Returns TRUE iff `result' is used in `merge' only as argument to gates
       of `merge'.  Uses outside of `merge' or one of its nested regions are
       ignored.  Note that the backedge argument of a loop merge doesn't count
       as "just gate" use, since this particular argument has to be live at the
       end of the region.  *)
      VAR
        use: D.Opnd;
      BEGIN
        use := result. useList;
        WHILE (use # NIL) DO
          IF merge(D.Merge). Dominates (use. instr. region) &
             ((use. instr. opcode # Opc.gate) OR
              (use. instr. region # merge) OR
              (merge. opcode = Opc.mergeLoop) & 
                (use. instr. opcode = Opc.gate) &
                (use. nextOpnd = NIL)) THEN
            RETURN FALSE
          END;
          use := use. nextUse
        END;
        RETURN TRUE
      END LocalGateArg;

    BEGIN
      NEW (lr);
      lr. next := NIL;
      lr. result := instr;
      
      IF (r IS D.Merge) & ~r. Dominates (instr. region) & 
         LocalGateArg (r, instr) THEN
        (* `instr' only serves as gate operand of a gate in `merge'; add it to
           the `gateArgs' list of this region, but don't add it to the list of
           global live ranges, and don't allocate a live range for it *)
        IF (rf. gateArgs = NIL) THEN
          rf. gateArgs := lr
        ELSE
          l := rf. gateArgs;
          WHILE (l. next # NIL) DO
            l := l. next
          END;
          l. next := lr
        END;
        instr. marker := gateArg
  
      ELSE
        (* add `instr' to end of list of global live ranges; this way the
           `marker' in `instr' will correspond to the position in this list;
           this is expected by [*] in procedure ColorGraph and [**] in 
           procedure IntegrateInstruction *)
        IF (rf. globals = NIL) THEN
          rf. globals := lr
        ELSE
          l := rf. globals;
          WHILE (l. next # NIL) DO
            l := l. next
          END;
          l. next := lr
        END;
  
        (* move global live range to the beginning of the index range; swap 
           index rf.lrCount with rf.globalCount;
           here holds: `instr. marker = summary. rf[reg]. regCount' *)
        instr. marker := rf. globalCount;
        rangeInfo[reg]. res[rf. globalCount](D.Result). marker := rf. lrCount;
        rangeInfo[reg]. res[rf. lrCount] := rangeInfo[reg]. res[rf. globalCount];
        rangeInfo[reg]. res[rf. globalCount] := instr;
  
        INC (rf. globalCount);
        INC (rf. lrCount)
      END
    END AddToGlobal;

  PROCEDURE AllocateRangeInfo (reg: SHORTINT; size: LONGINT);
  (* Makes sure that the bit matrix, live vector, and degree vector in
     `rangeInfo[reg]' are large enough to cope with `size' elements.  The
     matrix and vector are initialized to zero, respectively.  *)
    CONST
      initRows = 126;
      incrRows = 128;
    VAR
      rows, cols: LONGINT;
    BEGIN
      IF (size > rangeInfo[reg]. rows) THEN
        IF (rangeInfo[reg]. rows < 0) THEN
          rows := initRows
        ELSE
          rows := rangeInfo[reg]. rows
        END;
        REPEAT
          INC (rows, incrRows)
        UNTIL (size <= rows);
        cols := (rows+(bitsPerSet-1)) DIV bitsPerSet;

        NEW (rangeInfo[reg]. m, rows, cols);
        NEW (rangeInfo[reg]. v, cols);
        NEW (rangeInfo[reg]. d, rows);
        NEW (rangeInfo[reg]. s, rows);
        NEW (rangeInfo[reg]. ds, rows);
        rangeInfo[reg]. rows := rows;
        rangeInfo[reg]. cols := cols
      END;

      rangeInfo[reg]. currRows := size;
      rangeInfo[reg]. currCols := (size+(bitsPerSet-1)) DIV bitsPerSet;

      (* clear matrix *)
      FOR rows := 0 TO rangeInfo[reg]. currRows-1 DO
        rangeInfo[reg]. d[rows] := 0;
        FOR cols := 0 TO rangeInfo[reg]. currCols-1 DO
          rangeInfo[reg]. m[rows, cols] := {}
        END
      END;
      FOR cols := 0 TO rangeInfo[reg]. currCols-1 DO
        rangeInfo[reg]. v[cols] := {}
      END
    END AllocateRangeInfo;

  PROCEDURE Interfere (reg: SHORTINT; id: LONGINT);
  (* Make the live range denoted by `id' interfere with all ranges currently
     live.  In other word: add the bits in `v' to the ones in the matrix
     column `m[id]'.  *)
    VAR
      v: BitVector;
      m: BitMatrix;
    BEGIN
      v := rangeInfo[reg]. v;
      m := rangeInfo[reg]. m;
      FOR i := 0 TO rangeInfo[reg]. currCols-1 DO
        m[id, i] := m[id, i]+v[i]
      END;
    END Interfere;

  PROCEDURE AddToLive (reg: SHORTINT; id: LONGINT);
  (* Adds `id' to the current live vector of register file `reg'.  Also makes
     this live range interfere with all ranges currently live.  *)
    BEGIN
      Interfere (reg, id);
      INCL (rangeInfo[reg]. v[id DIV bitsPerSet], id MOD bitsPerSet)
    END AddToLive;

  PROCEDURE RemoveFromLive (result: D.Instruction);
  (* Removes `result' from the current live vector.  *)
    VAR
      reg: SHORTINT;
      i: LONGINT;
    BEGIN
      reg := TargetRegFile (result);
      i := result. marker;
      EXCL (rangeInfo[reg]. v[i DIV bitsPerSet], i MOD bitsPerSet)
    END RemoveFromLive;

  PROCEDURE SymmetricMatrix (reg: SHORTINT);
  (* Turns `rangeInfo[reg]. m' into a symmetric matrix by mirroring elements
     at the matrix diagonal.  This is necessary because the algorithm creating
     the matrix does not ensure the property that `i' interfering with `j'
     implies `j' interfering with `i' ("m[i,j] implies m[j,i]").  *)
    VAR
      x, y: LONGINT;
      m: BitMatrix;
    BEGIN
      m := rangeInfo[reg]. m;
      FOR y := 0 TO rangeInfo[reg]. currRows-1 DO
        FOR x := 0 TO rangeInfo[reg]. currRows-1 DO
          IF (x MOD bitsPerSet IN m[y, x DIV bitsPerSet]) THEN
            INCL (m[x, y DIV bitsPerSet], y MOD bitsPerSet)
          END
        END;
        (* clear diagonal *)
        EXCL (m[y, y DIV bitsPerSet], y MOD bitsPerSet)
      END
    END SymmetricMatrix;

  PROCEDURE IntegrateInstruction (instr: D.Instruction): D.Instruction;
  (* Adds instruction `instr' to the interference graph in `rangeInfo'.  The
     live vector is updated appropriately: `instr' is removed from the vector
     and its operands are added to it.
     Result is the instruction that has to be integrated next.  Normally this
     is `instr. prevInstr', unless `instr' happens to be a merge.  In the
     latter case all instructions belonging to the guard/merge sequence are
     handled together and the instruction in front of the entire sequence is
     returned.  *)
    VAR
      liveRange: D.Instruction;
      opnd: D.Opnd;
      reg: SHORTINT;
      lr, li, lj: LiveRangeList;
      i, j: LONGINT;
      ns: RegionSummary;

    PROCEDURE IntegrateMerge (merge: D.Merge): D.Instruction;
    (* Handle the sequence of instructions composed of guards and merges 
       passing control to `merge'.  For each of the different paths merging 
       into `merge' a corresponding live vector is computed that is used to
       scan the path.  Note that for every path out of a region in `r' the 
       interference information for the given region is computed; e.g. if the
       region is left through two different paths, then this happens twice.  *)
      VAR
        reg: SHORTINT;
        opn: INTEGER;
        needed, i, oldTop: LONGINT;
        new: BitVector;
        initial, final: ARRAY registerFiles OF LONGINT;
        prevInstr, h: D.Instruction;
        mergePath: D.Region;
        lr: LiveRangeList;

      PROCEDURE GateOpnd (merge: D.Merge; opn: INTEGER; res: D.Result):BOOLEAN;
      (* Returns TRUE if `res' if one of the uses of `res' is as argument #`opn' 
         in a gate of `merge'.  *)
        VAR
          use: D.Opnd;
        BEGIN
          use := res. useList;
          WHILE (use # NIL) &
                ((use. instr. opcode # Opc.gate) OR
                 (use. instr. region # merge) OR
                 (use. OperandIndex() # opn)) DO
            use := use. nextUse
          END;
          RETURN (use # NIL)
        END GateOpnd;

      BEGIN
        (* save the current contents of the live vectors and allocate space to
           hold the vectors valid at the beginning of the guard/merge complex;
           first find out how much space is needed, then make sure that the
           stack is large enough, and finally copy the stuff *)
        needed := 0;
        FOR reg := 0 TO registerFiles-1 DO
          INC (needed, rangeInfo[reg]. currCols)
        END;
        IF (liveStack = NIL) THEN
          NEW (liveStack, 1016);
          topStack := 0
        END;
        IF (topStack+needed*2 > LEN (liveStack^)) THEN
          NEW (new, ((topStack+needed*2+1027) DIV 1024)*1024-4);
          FOR i := 0 TO topStack-1 DO
            new[i] := liveStack[i]
          END;
          liveStack := new
        END;
        oldTop := topStack;
        FOR reg := 0 TO registerFiles-1 DO
          initial[reg] := topStack;
          FOR i := 0 TO rangeInfo[reg]. currCols-1 DO
            liveStack[topStack] := rangeInfo[reg]. v[i];
            INC (topStack)
          END;
          final[reg] := topStack;
          FOR i := 0 TO rangeInfo[reg]. currCols-1 DO
            liveStack[topStack] := {};
            INC (topStack)
          END
        END;

        (* trace region in front of `merge'; the scheduler has to make sure
           that they correspond to the paths into `merge'; the live vectors
           used at the end of every such path are always the vectors valid
           at the beginning of the merge *)
        prevInstr := merge. prevInstr;
        opnd := merge. opndList;
        opn := 1;
        WHILE (opnd # NIL) DO
          (* set `mergePath' to the neighbouring region in `merge. region'
             that dominates `opnd' *)
          mergePath := opnd. arg(D.Region);
          WHILE (mergePath. region # merge. region) DO
            mergePath := mergePath. region
          END;

          (* add all global live ranges that serve as argument to a gate
             operand corresponding to `mergePath' to the live vector *)
          FOR reg := 0 TO registerFiles-1 DO
            lr := merge. info(RegionSummary). rf[reg]. gateArgs;
            WHILE (lr # NIL) DO
              IF ~(lr. result. marker MOD bitsPerSet IN
                    rangeInfo[reg]. v[lr. result. marker DIV bitsPerSet]) &
                 GateOpnd (merge, opn, lr. result) THEN
                (* add all global live ranges reaching into `instr' to the live
                   vector; ignore all global live ranges that only appear as
                   operands of gates in the (non-loop) merge region `instr';
                   these ranges are treated specially in IntegrateMerge *)
                AddToLive (reg, lr. result. marker)
              END;
              lr := lr. next
            END
          END;

          h := IntegrateInstruction (mergePath);
          IF (h = NIL) OR Schedule.ExecutedBefore (h, prevInstr) THEN
            prevInstr := h
          END;
          opnd := opnd. nextOpnd;
          INC (opn);

          IF (opnd # NIL) THEN
            FOR reg := 0 TO registerFiles-1 DO
              FOR i := 0 TO rangeInfo[reg]. currCols-1 DO
                (* merge the current live vector (the one from the beginning of
                   `mergePath') with the one for the beginning of the guard/
                   merge complex *)
                liveStack[final[reg]+i] := liveStack[final[reg]+i]+
                                           rangeInfo[reg]. v[i];
                (* restore the live vector to the one that is valid at the
                   beginning of the merge *)
                rangeInfo[reg]. v[i] := liveStack[initial[reg]+i]
              END
            END
          END
        END;

        FOR reg := 0 TO registerFiles-1 DO
          (* update the current live vector to reflect the situation at the
             beginning of the guard/merge sequence; this vector is a union of 
             all life vectors from the beginnings of the merged paths *)
          FOR i := 0 TO rangeInfo[reg]. currCols-1 DO
            rangeInfo[reg]. v[i] := rangeInfo[reg]. v[i]+
                                    liveStack[final[reg]+i]
          END;
          
          (* all ranges live before guard/merge interfere; at this point the 
             interference between values used in different paths towards the
             merge isn't registred; therefore add the contents of the current
             live vector to the interference matrix *)
          FOR i := 0 TO rangeInfo[reg]. currRows-1 DO
            IF (i MOD bitsPerSet IN rangeInfo[reg]. v[i DIV bitsPerSet]) THEN
              Interfere (reg, i)
            END
          END
        END;
        topStack := oldTop;
        RETURN prevInstr
      END IntegrateMerge;

    BEGIN
      IF (instr IS D.Region) THEN
        (* integrate region `instr' into the interference graph of the current
           region `r'; use the information from `instr.info' *)
        ns := instr. info(RegionSummary);
        FOR reg := 0 TO registerFiles-1 DO
          lr := ns. rf[reg]. globals;
          WHILE (lr # NIL) DO
            IF instr(D.Region). Dominates (lr. result. region) THEN
              (* remove all global live ranges originating in `instr' from the
                 live vector *)
              RemoveFromLive (lr. result)
            END;
            lr := lr. next
          END;

          (* add all local ranges of `instr' to the live vector *)
          FOR i := ns. rf[reg]. localStart TO
                   ns. rf[reg]. localStart+ns. rf[reg]. localCount-1 DO
            INCL (rangeInfo[reg]. v[i DIV bitsPerSet], i MOD bitsPerSet)
          END;

          (* the local and global live ranges of region `instr' interfere with
             everything live at this point; additionally the local ones
             interfere with each other; note that at this point no global live
             ranges of `instr' are part of the live vector *)
          (* ... possible improvement: if control flow passes from `instr' into
             a merge, i.e. control never reaches the end of the region `instr'
             (because it's left directly or indirectly through merge(s)), then
             all live ranges _starting_ in `instr' cannot inferere with those
             elements of the live vector (the one valid just after `instr') 
             which _end_ within `instr.region'; the reason is that control will
             never pass from `instr' to `instr.nextInstr', but rather directly
             into the associated merge; this would improve register allocation
             for conditional expressions (&, OR), can't say if it would make a
             noticable difference, though *)
          FOR j := ns. rf[reg]. localStart TO
                   ns. rf[reg]. localStart+ns. rf[reg]. localCount-1 DO
            Interfere (reg, j)
          END;
          lr := ns. rf[reg]. globals;
          WHILE (lr # NIL) DO
            Interfere (reg, lr. result. marker);
            lr := lr. next
          END;

          (* remove all local ranges of `instr' from the live vector *)
          FOR i := ns. rf[reg]. localStart TO
                   ns. rf[reg]. localStart+ns. rf[reg]. localCount-1 DO
            EXCL (rangeInfo[reg]. v[i DIV bitsPerSet], i MOD bitsPerSet)
          END;
          
          (* if `instr' is a loop merge, add all arguments passed from the
             outside to its gates to the live vector *)
          IF (instr. opcode = Opc.mergeLoop) THEN
            lr := ns. rf[reg]. gateArgs;
            WHILE (lr # NIL) DO
              AddToLive (reg, lr. result. marker);
              lr := lr. next
            END
          END;

          (* add the interference matrix of the global ranges of region `instr'
             to the local matrix [**] *)
          i := 0;
          li := ns. rf[reg]. globals;
          WHILE (li # NIL) DO
            j := 0;
            lj := ns. rf[reg]. globals;
            WHILE (lj # NIL) DO
              IF (j MOD bitsPerSet IN ns.rf[reg].gi[i, j DIV bitsPerSet]) THEN
                INCL (rangeInfo[reg]. m[li. result. marker,
                                        lj. result. marker DIV bitsPerSet],
                      lj. result. marker MOD bitsPerSet)
              END;
              INC (j);
              lj := lj. next
            END;
            INC (i);
            li := li. next
          END;

          lr := ns. rf[reg]. globals;
          WHILE (lr # NIL) DO
            IF ~instr(D.Region). Dominates (lr. result. region) THEN
              (* add all global live ranges reaching into `instr' to the live
                 vector; ignore all global live ranges that only appear as
                 operands of gates in the (non-loop) merge region `instr';
                 these ranges are treated specially in IntegrateMerge *)
              AddToLive (reg, lr. result. marker)
            END;
            lr := lr. next
          END
        END
      ELSIF (instr. marker > noMark) & (instr. opcode # Opc.gate) THEN
        (* note that the live range of a gate starts at the beginning of the
           region it is part of *)
        RemoveFromLive (instr);
        
        IF (instr. useList = NIL) THEN
          (* this is a pathological case: the instruction leaves a result in
             a register, but its value is never used; in effect this 
             corresponds to an empty live range that interferes with nothing;
             but since a register is overwritten here, it does interfere with
             everything live at this point in practice *)
          Interfere (TargetRegFile (instr), instr. marker)
        END
      END;

      IF (instr IS D.Merge) & (instr. opcode # Opc.mergeLoop) THEN
        (* when scanning backwards over a (non-loop) merge the different paths
           into the merge have to be taken into consideration; every one of
           those paths is scanned separately until they converge again; the
           live vector before the merge/guard complex is the union of all
           live vectors derived through the different paths *)
        RETURN IntegrateMerge (instr(D.Merge))

      ELSIF (instr. opcode # Opc.gate) THEN
        (* do for normal instructions and guards, but not for gates:
           every argument of the instruction is checked whether it starts a
           live range and is placed into the live vector if does; note that
           the live ranges of gate arguments end at the beginning of the
           region that the gate is part of *)
        opnd := instr. opndList;
        WHILE (opnd # NIL) DO
          IF (opnd. arg IS D.Instruction) & opnd. ValueOperand() THEN
            liveRange := opnd. arg(D.Instruction);
            reg := TargetRegFile (liveRange);
            IF (reg >= 0) & (liveRange. marker > noMark) &
               ~((liveRange. marker MOD bitsPerSet) IN
                 rangeInfo[reg]. v[liveRange. marker DIV bitsPerSet]) THEN
              (* `liveRange' interferes with all live ranges currently
                  active: calculate union between bit matrix (column
                  `liveRange.marker') and the live vector *)
              AddToLive (reg, liveRange. marker)
            END
          END;
          opnd := opnd. nextOpnd
        END;
        RETURN instr. prevInstr

      ELSE
        RETURN instr. prevInstr
      END
    END IntegrateInstruction;

  PROCEDURE SetResult (reg: SHORTINT; id: LONGINT; res: D.Info);
  (* Adds `res' to the list of live ranges in `rangeInfo[reg]. res' at index
     `id'.  *)
    CONST
      initRows = 126;
      incrRows = 128;
    VAR
      rows, i: LONGINT;
      old, new: ResultVector;
    BEGIN
      IF (rangeInfo[reg]. res = NIL) OR (id >= LEN (rangeInfo[reg]. res^)) THEN
        IF (rangeInfo[reg]. res = NIL) THEN
          rows := initRows
        ELSE
          rows := rangeInfo[reg]. rows
        END;
        REPEAT
          INC (rows, incrRows)
        UNTIL (id < rows);
        
        (* allocate larger table *)
        old := rangeInfo[reg]. res;
        NEW (new, rows);
        IF (old # NIL) THEN
          FOR i := 0 TO LEN (old^, 0)-1 DO
            new[i] := old[i]
          END
        END;
        rangeInfo[reg]. res := new
      END;

      IF (res IS D.Instruction) THEN
        res(D.Instruction). marker := id
      ELSE
        res(Location). gid := id
      END;
      rangeInfo[reg]. res[id] := res
    END SetResult;

(*debug  PROCEDURE WriteLives (str: ARRAY OF CHAR; instr: D.Instruction);
    BEGIN
      Out.String (str);
      IF (instr # NIL) THEN
        Out.Char ("(");
        Out.LongInt (instr. pos, 0);
        Out.Char (")")
      END;
      Out.String (": ");
      FOR i := 0 TO summary. rf[0]. lrCount-1 DO
        IF (i MOD 32 IN rangeInfo[0]. v[i DIV 32]) THEN
          Out.String (" (");
          IF (rangeInfo[0]. res[i] IS D.Instruction) THEN
            Out.LongInt (rangeInfo[0]. res[i](D.Instruction). pos, 0);
          ELSE
            Out.Char ("x")
          END;
          Out.Char (")")
        END
      END;
      Out.Ln
    END WriteLives;*)
  
  BEGIN
    FOR reg := 0 TO registerFiles-1 DO
      regCount[reg] := 0
    END;

    (* preprocessing: assign an unique id to every result that writes to a
       register; determine the global live ranges that reach beyond the end of
       the region; use them to initialize the live vector valid after the last
       instruction of the region *)
    instr := r. instrTail;
    WHILE (instr # NIL) DO
      IF (instr IS D.Region) THEN
        (* integrate the global live ranges from region `instr' into the
           current region `r' *)
        FOR reg := 0 TO registerFiles-1 DO
          (* give all live ranges global to region `instr' an index (relative
             to `r') and add them to the global live ranges of `r' (if
             necessary; note that the local life ranges of `instr' are handled
             in a separate step *)
          lr := instr. info(RegionSummary). rf[reg]. globals;
          WHILE (lr # NIL) DO
            IF (lr. result. marker = noMark) THEN
              SetResult (reg, summary. rf[reg]. lrCount, lr. result);
              IF ~r. Dominates (lr. result. region) OR
                 NonlocalUse (lr. result, r) THEN
                (* `lr.result' is not just global to `instr' but to `r', too *)
                AddToGlobal (r, summary. rf[reg], reg, lr. result)
              ELSE
                INC (summary. rf[reg]. lrCount)
              END
            END;
            lr := lr. next
          END;
          
          lr := instr. info(RegionSummary). rf[reg]. gateArgs;
          WHILE (lr # NIL) DO
            IF (lr. result. marker = noMark) THEN
              SetResult (reg, summary. rf[reg]. lrCount, lr. result);
              IF ~r. Dominates (lr. result. region) OR
                 NonlocalUse (lr. result, r) THEN
                (* `lr.result' is not just global to `instr' but to `r', too *)
                AddToGlobal (r, summary. rf[reg], reg, lr. result)
              ELSE
                INC (summary. rf[reg]. lrCount)
              END
            END;
            lr := lr. next
          END
        END

      ELSE
        reg := TargetRegFile (instr);
        IF (instr. location = NIL) & (instr. marker = noMark) & (reg >= 0) THEN
          (* assumption: `instr' produces exactly one result stored in a
             register; assign an id to the result that is unique with respect
             to the given register file; the id values are stored in the
             `marker' field *)
          SetResult (reg, summary. rf[reg]. lrCount, instr);
          IF NonlocalUse (instr, r) THEN
            (* `instr' describes a live range that originates in `r' but
               extends beyond it *)
            AddToGlobal (r, summary. rf[reg], reg, instr)
          ELSE
            INC (summary. rf[reg]. lrCount)
          END
        END
      END;

      IF ~(instr IS D.Merge) THEN
        opnd := instr. opndList;
        WHILE (opnd # NIL) DO
          IF (opnd. arg IS D.Instruction) &
             (opnd. arg(D.Instruction). marker = noMark) &
             (opnd. arg(D.Instruction). location = NIL) &
             ~r. Dominates (opnd. arg(D.Instruction). region) THEN
            (* `opnd' takes as argument a result that is generated outside the
               current region: add it to the list of global live ranges *)
            liveRange := opnd. arg(D.Instruction);
            reg := TargetRegFile (liveRange);
            IF (reg >= 0) THEN
              SetResult (reg, summary. rf[reg]. lrCount, liveRange);
              AddToGlobal (r, summary. rf[reg], reg, liveRange)
            END
          END;
          opnd := opnd. nextOpnd
        END
      END;

      instr := instr. prevInstr
    END;

    region := r. regionList;
    WHILE (region # NIL) DO
      (* add as many live ranges as there are registers used in `region'; these
         live ranges represent registers used up in the nested region and
         aren't bound to a specific result *)
      ns := region. info(RegionSummary);
      FOR reg := 0 TO registerFiles-1 DO
        ns. rf[reg]. localStart := summary. rf[reg]. lrCount;
        FOR i := 0 TO ns. rf[reg]. localCount-1 DO
          SetResult (reg, summary. rf[reg]. lrCount,
                     ns. rf[reg]. locations[ns. rf[reg]. globalCount+i]);
          INC (summary. rf[reg]. lrCount)
        END
      END;
      region := region. nextRegion
    END;

    FOR reg := 0 TO registerFiles-1 DO
      (* create an empty bit matrix to hold the interference information *)
      AllocateRangeInfo (reg, summary. rf[reg]. lrCount)
    END;

    (* initialize the live vectors with all global live ranges that either
       start in region `r', or are used in `r' and at some place after `r' *)
    FOR reg := 0 TO registerFiles-1 DO
      lr := summary. rf[reg]. globals;
      WHILE (lr # NIL) DO
        IF r. Dominates (lr. result. region) OR
           LiveAcrossRegion (lr. result, r) THEN
          AddToLive (reg, lr. result. marker);
        END;
        lr := lr. next
      END
    END;

    (* if `r' is a loop merge, add the backedge operands of all loop gates to
       the live vector *)
    IF (r. opcode = Opc.mergeLoop) THEN
      use := r. useList;
      WHILE (use # NIL) DO
        IF (use. instr. opcode = Opc.gate) THEN
          arg := use. nextOpnd. nextOpnd. arg;
          IF (arg IS D.Instruction) THEN
            reg := TargetRegFile (arg(D.Instruction));
            IF(reg >= 0) THEN
              AddToLive (reg, arg(D.Instruction). marker)
            END
          END
        END;
        use := use. nextUse
      END
    END;

    (* build interference matrix; basically this is a simple scan backwards
       over all instructions that fills in the interference matrix and updates
       the live vector on the way; things are slightly complicated by the fact
       that scanning through a merge has to treat the paths into the merge
       different from other instructions/guards (see IntegrateMerge) *)
    instr := r. instrTail;
    WHILE (instr # NIL) DO
      instr := IntegrateInstruction (instr)
    END;

    (* make the interference matrices symmetric by mirroring the elements at
       the diagonal *)
    FOR reg := 0 TO registerFiles-1 DO
      SymmetricMatrix (reg)
    END
  END BuildInterferenceGraphs;

(*debug PROCEDURE WriteMatrix (VAR r: RangeInfo);
  VAR
    i, j: LONGINT;
  
  PROCEDURE Id (i: LONGINT);
    BEGIN
      Out.String(" (");
      IF (r. res[i] IS D.Instruction) THEN
        Out.LongInt (r. res[i](D.Instruction). pos, 0)
      ELSE
        Out.LongInt (SYSTEM.VAL (LONGINT, r. res[i]), 0)
      END;
      Out.String (")");
    END Id;
  
  BEGIN
    Out.String ("Collision matrix: "); Out.Ln;
    FOR i := 0 TO r. currRows-1 DO
      Id (i);
      Out.String (": ");
      FOR j := 0 TO r. currRows-1 DO
        IF (j MOD bitsPerSet IN r. m[i, j DIV bitsPerSet]) THEN
          Id (j)
        END
      END;
      Out.Ln
    END
  END WriteMatrix;*)

PROCEDURE CoalesceRanges (r: D.Region; summary: RegionSummary);
(* Attempt to coalesce live ranges of gates in nested merges with their
   respective arguments.  *)
  VAR
    instr: D.Instruction;
    region: D.Region;
    reg: SHORTINT;
    ns: RegionSummary;
    i: LONGINT;
    
  PROCEDURE ScanGates (merge: D.Merge; loopBackedge: BOOLEAN);
    VAR
      opnd, use: D.Opnd;
      gateId: LONGINT;
    
    PROCEDURE LiveRangeId (instr: D.Instruction; reg: SHORTINT): LONGINT;
      BEGIN
        IF (instr. marker < summary. rf[reg]. lrCount) &
           (rangeInfo[reg]. res[instr. marker] = instr) THEN
          RETURN instr. marker
        ELSE
          RETURN instr. location(Location). gid
        END
      END LiveRangeId;
    
    PROCEDURE TryCoalescing (gateId: LONGINT; reg: SHORTINT; arg: D.Usable);
      VAR
        argId: LONGINT;
        
      PROCEDURE Merge (src, dest: LONGINT);
        VAR
          m: BitMatrix;
          i: LONGINT;
        BEGIN
          m := rangeInfo[reg]. m;
          FOR i := 0 TO rangeInfo[reg]. currCols-1 DO
            m[dest, i] := m[dest, i]+m[src, i]
          END;
          FOR i := 0 TO rangeInfo[reg]. currRows-1 DO
            IF (src MOD bitsPerSet IN m[i, src DIV bitsPerSet]) THEN
              INCL (m[i, dest DIV bitsPerSet], dest MOD bitsPerSet)
            END
          END;
          
          (* mark live range `src' as being coalesced with `dest'; in the
             following steps it it has to be treated as an empty range;
             it must not get an location and its live range id should be 
             identified with `dest' *)
          rangeInfo[reg]. d[src] := -dest-1  (* has to be negative *)
        END Merge;
      
      BEGIN
        WITH arg: D.Instruction DO
          IF (arg. opcode # Opc.adr) THEN  
            (* note that adr instructions don't have a live range for the 
               ANSI-C back-end *)
               
            argId := LiveRangeId (arg, reg);
            WHILE (rangeInfo[reg]. d[argId] < 0) DO
              argId := -rangeInfo[reg]. d[argId]-1
            END;

            (* coalesce live ranges if they do not interfere; two global life 
               ranges are never coalesced since they may interfere with each 
               other in the enclosing region; gate arguments are always global
               (though in a special way), the gate itself can be local *)
            IF (gateId # argId) &
               ((gateId >= summary. rf[reg]. globalCount) OR
                (argId >= summary. rf[reg]. globalCount)) &
               ~(argId MOD bitsPerSet IN 
                 rangeInfo[reg]. m[gateId, argId DIV bitsPerSet]) &
               ~(gateId MOD bitsPerSet IN 
                 rangeInfo[reg]. m[argId, gateId DIV bitsPerSet]) THEN
              (* gate and argument do not interfere: coalesce the argument's
                 live range with that of the gate; by swapping the id with the 
                 higher value with the one with the lower it's guaranteed that 
                 the source is never a global live range *)
              IF (argId > gateId) THEN
                Merge (argId, gateId)
              ELSE
                Merge (gateId, argId)
              END
            END
          END
        ELSE
          (* ignore undefined values (arg IS D.Object) and constants (arg IS
             D.Const); only instructions write to registers, therefore results
             (arg IS D.Result) are ignored, too *)
        END
      END TryCoalescing;
    
    BEGIN
      use := merge. useList;
      WHILE (use # NIL) DO
        IF (use. instr. opcode = Opc.gate) THEN 
          reg := TargetRegFile (use. instr);
          IF (reg >= 0) THEN
            gateId := LiveRangeId (use. instr, reg);
            WHILE (rangeInfo[reg]. d[gateId] < 0) DO
              gateId := -rangeInfo[reg]. d[gateId]-1
            END;
            
            IF loopBackedge THEN
              TryCoalescing (gateId, reg, use. nextOpnd. nextOpnd. arg);
            ELSIF (merge. opcode = Opc.mergeLoop) THEN
              TryCoalescing (gateId, reg, use. nextOpnd. arg);
            ELSE
              opnd := use. nextOpnd;
              WHILE (opnd # NIL) DO
                TryCoalescing (gateId, reg, opnd. arg);
                IF (rangeInfo[reg]. d[gateId] < 0) THEN
                  gateId := -rangeInfo[reg]. d[gateId]-1
                END;
                opnd := opnd. nextOpnd
              END
            END
          END
        END;
        use := use. nextUse
      END
    END ScanGates;
  
  BEGIN
    IF (r. opcode = Opc.mergeLoop) THEN
      ScanGates (r(D.Merge), TRUE)
    END;
    
    instr := r. instrTail;
    WHILE (instr # NIL) DO
      IF (instr IS D.Merge) THEN
        ScanGates (instr(D.Merge), FALSE)
      END;
      instr := instr. prevInstr
    END;
    
    (* clean up `gid' attribute of locations in nested regions *)
    region := r. regionList;
    WHILE (region # NIL) DO
      ns := region. info(RegionSummary);
      FOR reg := 0 TO registerFiles-1 DO
        FOR i := 0 TO ns. rf[reg]. localCount-1 DO
          ns. rf[reg]. locations[i]. gid := noMark
        END
      END;
      region := region. nextRegion
    END
  END CoalesceRanges;

PROCEDURE ColorGraph (r: D.Region; VAR ri: RangeInfo;
                      reg: SHORTINT; VAR rf: RegFileSummary);
(* Creates a coloring for the graph described by `ri. m'.  Every color 
   corresponds to a location value.  Every live range in `r' is assigned a
   location in such a way, that two interfering live ranges are assigned 
   different locations.
   pre: for every coalesced live range `i' the value of `ri.d[i]' is 
     negative and denotes the range it has been coalesced with; for all other
     live ranges `j' `ri.d[j]' is zero.  *)
  VAR
    m: BitMatrix;
    d, s, ds: LongintVector;
    h, i, j, k, c, rows, activeLR: LONGINT;
    lr: LiveRangeList;
    region: D.Region;
    loc: Location;

  PROCEDURE CreateLocation;
    VAR
      l: Location;
      new: LocationVector;
      i: LONGINT;
    BEGIN
      l := NewLoc ("");

      IF (locVector = NIL) THEN
        NEW (locVector, 64)
      ELSIF (locCount >= LEN (locVector^)) THEN
        NEW (new, LEN (locVector^)+64);
        FOR i := 0 TO LEN (locVector^)-1 DO
          new[i] := locVector[i]
        END;
        locVector := new
      END;

      locVector[locCount] := l;
      INC (locCount)
    END CreateLocation;

  PROCEDURE SiftToLeaf (i, n: LONGINT);
  (* sift: move s[i] to its correct position in the heap s[i..n-1] *)
    VAR
      j, x: LONGINT;
    BEGIN
      i := i; j := 2*i+1; x := s[i];
      IF (j < n) & (d[s[j]] > d[s[j+1]]) THEN
        INC (j)
      END;
      WHILE (j <= n) & (d[x] > d[s[j]]) DO
        (* here holds: `j' refers to the smallest son of `i' *)
        s[i] := s[j]; ds[s[i]] := i; i := j; j := 2*i+1;
        IF (j < n) & (d[s[j]] > d[s[j+1]]) THEN
          INC (j)
        END
      END;
      s[i] := x; ds[x] := i
    END SiftToLeaf;
  
  PROCEDURE BuildHeap (n: LONGINT);
    VAR
      l: LONGINT;
    BEGIN
      l := ((n-1) DIV 2)+1;
      WHILE (l # 0) DO
        DEC (l); SiftToLeaf (l, n)
      END
    END BuildHeap;
  
  BEGIN
    m := ri. m; d := ri. d; s := ri. s; ds := ri. ds;
    rows := ri. currRows;

    (* determine the degree (i.e. the number of neighbours) of every node in
       the interference graph *)
    FOR i := 0 TO rows-1 DO
      IF (d[i] >= 0) THEN
        FOR c := 0 TO rows-1 DO
          IF (c MOD bitsPerSet IN m[i, c DIV bitsPerSet]) THEN
            INC (d[i])
          END
        END
      END
    END;

    (* remove the node with the smallest current degree from the graph and push
       it on a stack; lower the degree of all it's neighbours; repeat until all
       nodes are removed; afterwards color the nodes in reverse order of
       deletion;  note: this approach can't be used when coloring with a
       limited number of colors (i.e. registers), since it'll deliver a
       coloring but may use arbitrary many colors to do so; in particular no
       live ranges are spilled; see [Bri92] how to built a k coloring and deal
       with spilling (although Briggs doesn't talk about hierarchical graph
       coloring in particular) *)
    (* initialize list of nodes; the array is also used to hold the stack; 
       skip live ranges that where coalesced away *)
    activeLR := 0;
    FOR i := 0 TO rows-1 DO
      IF (d[i] >= 0) THEN
        s[activeLR] := i;
        ds[i] := activeLR;
        INC (activeLR)
      END
    END;
    BuildHeap (activeLR-1);
    h := activeLR-1;
    WHILE (h > 0) DO
      (* swap the index of the node with the smallest degree to array position 
         `h' *)
      c := s[0]; s[0] := s[h]; s[h] := c; 
      ds[s[0]] := 0; ds[s[h]] := h;
      DEC (h);
      IF (h > 0) THEN
        SiftToLeaf (0, h);

        (* lower degree of all neighbours of node `c', adjust heap structure *)
        FOR i := 0 TO rows-1 DO
          IF (d[i] >= 0) & (i MOD bitsPerSet IN m[c, i DIV bitsPerSet]) THEN
            DEC (d[i]);
            j := ds[i];
            IF (j <= h) THEN
              (* sink towards root *)
              WHILE (j > 0) & (d[s[j]] < d[s[(j-1) DIV 2]]) DO
                k := s[j]; s[j] := s[(j-1) DIV 2]; s[(j-1) DIV 2] := k;
                ds[s[j]] := j; ds[s[(j-1) DIV 2]] := (j-1) DIV 2;
                j := (j-1) DIV 2
              END
            END
          END
        END
      END
    END;

    (* color graph by adding successively the nodes indicated by s[0], s[1],
       .., s[activeLR-1] and choosing appropriate colors for them; the colors
       are represented by the location attributes of the live ranges *)
    locCount := 0;
    FOR i := 0 TO activeLR-1 DO
      (* clear `used' flag in the existing locations *)
      FOR c := 0 TO locCount-1 DO
        locVector[c]. used := FALSE
      END;

      (* turn on `used' for all neighbours of `s[i]' *)
      FOR c := 0 TO rows-1 DO
        IF (c MOD bitsPerSet IN m[s[i], c DIV bitsPerSet]) THEN
          IF (ri. res[c] IS Location) THEN
            IF (ri. res[c](Location). outerLocation # NIL) THEN
              ri. res[c](Location). outerLocation. used := TRUE
            END
          ELSIF (ri. res[c](D.Result). location # NIL) THEN
            ri. res[c](D.Result). location(Location). used := TRUE
          END
        END
      END;

      (* assign the first location to `s[i]' that isn't used by one of its
         neighbours; if all locations are used, create a new one and use it *)
      c := 0;
      WHILE (c # locCount) & locVector[c]. used DO
        INC (c)
      END;
      IF (c = locCount) THEN  (* create new location *)
        CreateLocation
      END;
      IF (ri. res[s[i]] IS Location) THEN
        ri. res[s[i]](Location). outerLocation := locVector[c]
      ELSE
        ri. res[s[i]](D.Result). location := locVector[c]
      END
    END;

    (* assign locations to ranges that were previously coalesced with another
       ranges *)
    FOR i := 0 TO rows-1 DO
      IF (d[i] < 0) THEN
        h := -d[i]-1;
        WHILE (d[h] < 0) DO
          h := -d[h]-1
        END;
          
        IF (ri. res[h] IS Location) THEN
          loc := ri. res[h](Location). outerLocation
        ELSE
          loc := ri. res[h](D.Result). location(Location)
        END;
        
        IF (ri. res[i] IS Location) THEN
          ri. res[i](Location). outerLocation := loc
        ELSE
          ri. res[i](D.Result). location := loc
        END
      END
    END;
    
    (* for every nested region connect the (locally used) locations of global
       live ranges to the ones assigned to them in the enclosing region [*] *)
    region := r. regionList;
    WHILE (region # NIL) DO
      i := 0;
      lr := region. info(RegionSummary). rf[reg]. globals;
      WHILE (lr # NIL) DO
        region. info(RegionSummary). rf[reg]. locations[i]. outerLocation :=
          lr. result. location(Location);
        INC (i);
        lr := lr. next
      END;
      region := region. nextRegion
    END;

    (* put the list of assigned locations into the summary; place the locations
       of global live ranges at the beginning and append the rest to it *)
    NEW (rf. locations, locCount);
    FOR c := 0 TO locCount-1 DO
      locVector[c]. used := FALSE
    END;
    lr := rf. globals;
    WHILE (lr # NIL) DO
      rf. locations[lr. result. marker] := lr. result. location(Location);
      lr. result. location(Location). used := TRUE;
      lr := lr. next
    END;
    (* here holds:
    FOR c := 0 TO rf. globalCount-1 DO
      ASSERT (rf. locations[c] = ri. res[c](D.Instruction). location)
    END;
    *)
    h := rf. globalCount;
    FOR c := 0 TO locCount-1 DO
      IF ~locVector[c]. used THEN
        rf. locations[h] := locVector[c];
        INC (h)
      END
    END;
    rf. localCount := locCount-rf.globalCount
  END ColorGraph;

PROCEDURE UpdateSummary (VAR ri: RangeInfo; VAR rf: RegFileSummary);
(* Put the information that is important to the enclosing region into the
   `summary' block.  In particular put a copy of the part of the interference
   graph dealing with global live ranges into the summary.  *)
  VAR
    rows, cols, r, c: LONGINT;
  BEGIN
    (* copy that part of interference graph into the summary that describes
       the relationship between all global live ranges *)
    IF (rf. globalCount > 0) THEN
      rows := rf. globalCount;
      cols := (rows+(bitsPerSet-1)) DIV bitsPerSet;
      NEW (rf. gi, rows, cols);
      FOR r := 0 TO rows-1 DO
        FOR c := 0 TO cols-1 DO
          rf. gi[r, c] := ri. m[r, c]
        END
      END
    END
  END UpdateSummary;

PROCEDURE Region (r: D.Region);
(* Assigns locations to all live ranges in `r' that are passed in "registers".
   After all nested regions have been completed, an interference graph for the
   live ranges in `r' is created.  Then the nodes of this graph are assigned a
   (hopefully small) number of colors.  Every color corresponds to a register
   location.  
   The results of this process are returned in `r. info' in form of a object of
   type `RegionSummary'.  For every register file it contains the number of
   registers used to hold local values of `r', a list of the live ranges of 
   used in `r' (represented by instances of `Instruction'), an interference 
   matrix describing conflicts between the global live ranges, and a list of
   locations that were assigned to the global/local ranges in `r'.  *)
  VAR
    region: D.Region;
    summary: RegionSummary;
    lr: LiveRangeList;
    reg: SHORTINT;

  PROCEDURE InterfereGlobalRanges (VAR ri: RangeInfo; VAR rf: RegFileSummary);
  (* Add interference edges between all global live ranges.  *)
    VAR
      x, y: LONGINT;
    BEGIN
      FOR y := 0 TO rf. globalCount-1 DO
        FOR x := 0 TO rf. globalCount-1 DO
          IF (x # y) THEN
            INCL (ri. m[y, x DIV bitsPerSet], x MOD bitsPerSet)
          END
        END
      END
    END InterfereGlobalRanges;

  PROCEDURE CorrectGlobalInterference (VAR ri: RangeInfo;
                                       VAR rf: RegFileSummary);
  (* For every global live range R that shares its location with local ones,
     add interference information between locations of global live ranges.
     That is, if two global live ranges G0 and G1 have been assigned the
     locations L0 and L1, and there exist local live ranges that also have L0
     and L1 as their location, and L0 interferes with L1 in one of these
     ranges, then mark G0 and G1 as interfering for the enclosing region.  *)
    VAR
      i, j, id0, id1: LONGINT;
      m, gi: BitMatrix;
    BEGIN
      (* replace elements of `ri. res' with the respective location that was
         assigned to the given index in region `r'; locations corresponding
         to global live ranges are given a `gid' field that holds the global
         live range's index, all other `gid' are left at `noMark'  *)
      FOR i := 0 TO rf. globalCount-1 DO
        ri. res[i] := ri. res[i](D.Instruction). location;
        ri. res[i](Location). gid := i
      END;
      FOR i := rf. globalCount TO rf. lrCount-1 DO
        IF (ri. res[i] IS D.Instruction) THEN
          ri. res[i] := ri. res[i](D.Instruction). location
        ELSE
          ri. res[i] := ri. res[i](Location). outerLocation
        END
      END;

      (* extend the interference between locations to their counterparts in the
         set of global live ranges *)
      m := ri. m;
      gi := rf. gi;
      FOR i := 0 TO rf. lrCount-1 DO
        IF (ri. res[i](Location). gid > noMark) THEN
          id0 := ri. res[i](Location). gid;
          FOR j := i+1 TO rf. lrCount-1 DO
            IF (j MOD bitsPerSet IN m[i, j DIV bitsPerSet]) &
               (ri. res[j](Location). gid > noMark) THEN
              id1 := ri. res[j](Location). gid;
              INCL (gi[id0, id1 DIV bitsPerSet], id1 MOD bitsPerSet);
              INCL (gi[id1, id0 DIV bitsPerSet], id0 MOD bitsPerSet)
            END
          END
        END
      END
    END CorrectGlobalInterference;

(*debug  PROCEDURE WriteRegionInfo (r: D.Region; VAR rf: RegFileSummary);
    VAR
      l: LiveRangeList;
      i, j: LONGINT;
      
    PROCEDURE WriteGlobal (i: LONGINT);
      VAR
        l: LiveRangeList;
      BEGIN
        l := rf. globals;
        WHILE (i # 0) DO
          l := l. next;
          DEC (i)
        END;
        Out.String (" (");
        Out.LongInt (l. result. pos, 0);
        Out.Char (")")
      END WriteGlobal;
    
    BEGIN
      Out.String ("REGION (");
      Out.LongInt (r. pos, 0);
      Out.Char (")");
      Out.Ln;
      Out.LongInt (rf. globalCount, 0);
      Out.String (" global live ranges:");
      l := rf. globals;
      WHILE (l # NIL) DO
        Out.String (" (");
        Out.LongInt (l. result. pos, 0);
        Out.Char (")");
        l := l. next
      END;
      Out.Ln;
      Out.String ("global interference: "); Out.Ln;
      FOR i := 0 TO rf. globalCount-1 DO
        WriteGlobal (i); Out.String (":");
        FOR j := 0 TO rf. globalCount-1 DO
          IF (j MOD 32 IN rf. gi[i, j DIV 32]) THEN
            WriteGlobal (j)
          END
        END;
        Out.Ln
      END;
      Out.String ("gate args:");
      l := rf. gateArgs;
      WHILE (l # NIL) DO
        Out.String (" (");
        Out.LongInt (l. result. pos, 0);
        Out.Char (")");
        l := l. next
      END;
      Out.Ln;
      Out.String ("local live ranges: ");
      Out.LongInt (rf. localCount, 0);
      Out.Ln;
      Out.Ln;
    END WriteRegionInfo;
  
  PROCEDURE WriteLocations (r: D.Region; VAR rf: RegFileSummary);
    VAR
      i: LONGINT;
      g: LiveRangeList;
      
    PROCEDURE Propagate (r: D.Region; reg: SHORTINT);
    (* Propagate the assignment of locations to variable names in `r' to its 
       nested regions.  *)
      VAR
        region: D.Region;
        i: LONGINT;
        summary: RegionSummary;
      BEGIN
        region := r. regionList;
        WHILE (region # NIL) DO
          summary := region. info(RegionSummary);
          FOR i := 0 TO summary. rf[reg]. globalCount+
                        summary. rf[reg]. localCount-1 DO
            summary. rf[reg]. locations[i]. value :=
              summary. rf[reg]. locations[i]. outerLocation. value
          END;
          Propagate (region, reg);
          region := region. nextRegion
        END
      END Propagate;

    PROCEDURE WrInstr (instr: D.Instruction; off: INTEGER);
      VAR
        i: INTEGER;
        opnd: D.Opnd;
        
      PROCEDURE WrLocation (l: D.Location);
        BEGIN
          IF (l # NIL) & (l IS Location) THEN
            IF l(Location). value = NIL THEN
              Out.String ("NIL")
            ELSE
              Out.String (l(Location). value^)
            END
          END
        END WrLocation;
      
      BEGIN
        Out.Ln;
        FOR i := 0 TO off-1 DO
          Out.String ("  ")
        END;
        Out.Char ("(");
        Out.LongInt (instr. pos, 0);
        Out.String (") ");
        WrLocation (instr. location);
        Out.String (" ");
        WriteGSA.WrOpcode (instr. opcode);
        opnd := instr. opndList;
        WHILE (opnd # NIL) DO
          Out.Char (" ");
          IF (opnd. arg IS D.Result) THEN
            WrLocation (opnd. arg(D.Result). instr. location)
          END;
          opnd := opnd. nextOpnd
        END;
        IF (instr IS D.Region) THEN
          instr := instr(D.Region). instrList;          
          WHILE (instr # NIL) DO
            WrInstr (instr, off+1);
            instr := instr. nextInstr
          END
        END
      END WrInstr;

    BEGIN
      Out.String ("LOCATIONS (");
      Out.LongInt (r. pos, 0);
      Out.String (") ");
      Out.Ln;
      (* install locations *)
      g := rf. globals;
      FOR i := 0 TO rf. globalCount+rf. localCount-1 DO
        NEW (rf. locations[i]. value, 8);
        IntStr.IntToStr (i, rf. locations[i]. value^);
        IF (i < rf. globalCount) THEN
          Strings.Insert ("gL", 0, rf. locations[i]. value^);
          Out.String ("  (");
          Out.LongInt (g. result. pos, 0);
          Out.String ("): ");
          Out.String (rf. locations[i]. value^);
          Out.Ln;
          g := g. next
        ELSE
          Strings.Insert ("lL", 0, rf. locations[i]. value^)
        END
      END;
      (* propagate locations *)
      Propagate (r, 0);
      (* write locations *)
      WrInstr (r, 0);
      (* cleanup *)
      FOR i := 0 TO rf. globalCount+rf. localCount-1 DO
        rf. locations[i]. value := NIL
      END;
      Propagate (r, 0)
    END WriteLocations;*)
  
  BEGIN
    (* do register allocation for all regions nested in `r'; the results will
       be stored in `region.info' *)
    region := r. regionList;
    WHILE (region # NIL) DO
      Region (region);
      region := region. nextRegion
    END;

    (* allocate memory block to hold region summary *)
    NEW (summary);
    FOR reg := 0 TO registerFiles-1 DO
      summary. rf[reg]. globalCount := 0;
      summary. rf[reg]. globals := NIL;
      summary. rf[reg]. gateArgs := NIL;
      summary. rf[reg]. localCount := 0;
      summary. rf[reg]. localStart := -1;
      summary. rf[reg]. gi := NIL;
      summary. rf[reg]. locations := NIL;
      summary. rf[reg]. lrCount := 0
    END;
    r. info := summary;

    BuildInterferenceGraphs (r, summary);
    CoalesceRanges (r, summary);
    FOR reg := 0 TO registerFiles-1 DO
      IF (summary. rf[reg]. lrCount # 0) THEN
        UpdateSummary (rangeInfo[reg], summary. rf[reg]);
        InterfereGlobalRanges (rangeInfo[reg], summary. rf[reg]);
        ColorGraph (r, rangeInfo[reg], reg, summary. rf[reg]);
        CorrectGlobalInterference (rangeInfo[reg], summary. rf[reg]);

        (* set markers of global live ranges to `noMark' and clear their
           `location' attribute; this is necessary because the indices assigned
           in this procedure are only valid for region `r'; the next invocation
           of `BuildInterferenceGraphs' expects them to be cleared *)
        lr := summary. rf[reg]. globals;
        WHILE (lr # NIL) DO
          lr. result. marker := noMark;
          lr. result. location := NIL;
          lr := lr. next
        END
      END;
      
      (* cleanup the special global results marked with `gateArg' *)
      lr := summary. rf[reg]. gateArgs;
      WHILE (lr # NIL) DO
        lr. result. marker := noMark;
        lr := lr. next
      END
    END
  END Region;


PROCEDURE ClearVariables;
  VAR
    i: INTEGER;
  BEGIN
    FOR i := 0 TO registerFiles-1 DO
      rangeInfo[i]. rows := -1;
      rangeInfo[i]. cols := -1;
      rangeInfo[i]. currRows := -1;
      rangeInfo[i]. currCols := -1;
      rangeInfo[i]. m := NIL;
      rangeInfo[i]. v := NIL;
      rangeInfo[i]. d := NIL;
      rangeInfo[i]. s := NIL;
      rangeInfo[i]. res := NIL
    END;
    locCount := -1;
    locVector := NIL;
    liveStack := NIL;
    topStack := -1;
    
    FOR i := 0 TO LEN (allocCounter)-1 DO
      allocCounter[i] := 0
    END
  END ClearVariables;

PROCEDURE GlobalRegion* (greg: D.GlobalRegion);
(* Assign locations to all values in `greg' that are passed in "registers".
   pre: Class.Region has been run on `greg' *)
  VAR
    reg: SHORTINT;
    i: LONGINT;
    summary: RegionSummary;

  PROCEDURE AssignRegisters (VAR rf: RegFileSummary; prefix: ARRAY OF CHAR);
  (* Assign a variable name to every local live range in register file `rf'
     of `greg'.  Use `prefix' as name prefix.  *)
    VAR
      i: LONGINT;
    BEGIN
      FOR i := 0 TO rf. localCount-1 DO
        NEW (rf. locations[i]. value, 8);
        IntStr.IntToStr (i, rf. locations[i]. value^);
        Strings.Insert (prefix, 0, rf. locations[i]. value^)
      END
    END AssignRegisters;

  PROCEDURE PropagateRegisters (r: D.Region; reg: SHORTINT);
  (* Propagate the assignment of locations to variable names in `r' to its 
     nested regions.  *)
    VAR
      region: D.Region;
      i: LONGINT;
      summary: RegionSummary;
    BEGIN
      region := r. regionList;
      WHILE (region # NIL) DO
        summary := region. info(RegionSummary);
        FOR i := 0 TO summary. rf[reg]. globalCount+
                      summary. rf[reg]. localCount-1 DO
          summary. rf[reg]. locations[i]. value :=
            summary. rf[reg]. locations[i]. outerLocation. value
        END;
        PropagateRegisters (region, reg);
        region := region. nextRegion
      END
    END PropagateRegisters;

  PROCEDURE MemoryLocations (r: D.Region);
  (* Handle all location attributes in `r' that do not correspond to registers,
     but rather memory locations.  Fix GSA instructions that are functions in
     GSA but not C by erasing all references to their (not available) function
     results.  *)
    VAR
      opc: INTEGER;
      instr, next: D.Instruction;
      res: D.Result;
      opnd: D.Opnd;
      obj: D.Object;
    BEGIN
      instr := r. instrList;
      WHILE (instr # NIL) DO
        next := instr. nextInstr;
        WITH instr: D.Region DO
          MemoryLocations (instr)
        ELSE
          opc := instr. opcode;

          IF (Class.instrVoid IN instr. flags) &
             ((opc = Opc.boundIndex) OR  (opc = Opc.boundRange) OR
              (opc = Opc.typeGuard)) THEN
            (* these instructions are plain functions in GSA, but not in C:
               they are translated into plain statements;  to avoid references
               to their non-existent result they are replaced by their
               respective index argument;  note that this replacement has to be
               done after instruction scheduling, or the range check may end up
               after the array/set access *)
            instr. ReplaceUses (instr. opndList. arg)
          
          ELSIF (opc = Opc.typeCast) &
                (Class.RegClass (instr. type) = 
                 Class.RegClass (instr. opndList. OpndType())) THEN
            (* remove type cast if source and target are located in the same
               register file *)
            instr. ReplaceUses (instr. opndList. arg);
            instr. Delete();
            opc := -1
          END;

          IF (opc = Opc.adr) THEN
            (* address values are not stored in variables, but rather
               integrated directly into the emitted code; note that here I'm
               using the location attribute to hold an r-value *)
            instr. location := GetAddressValue (greg, instr. opndList. arg,
                                                TRUE)
          
          ELSIF (opc = Opc.typeCast) THEN
            opnd := instr. opndList;
            IF (opnd. location # NIL) THEN
              obj := opnd. location(D.SymLocation). var(D.Object);
              INCL (obj. beFlags, StdTypes.objUsedLocalVar)
            END
          END;
          
          CASE opc OF
          | Opc.call, Opc.accessMem, Opc.updateMem, Opc.bit, Opc.move:
            (* for every intruction that reads from $mem scan list of local
               variables that are forced into memory; every variable is marked
               so that a declaration is emitted for it when generating the
               function *)
            opnd := instr. GetOperand (Sym.mem, D.symLocObject);
            IF (opnd # NIL) THEN
              opnd := opnd. nextOpnd. nextOpnd;  (* skip $mem and $store *)
              WHILE (opnd # NIL) DO
                obj := opnd. location(D.SymLocation). var(D.Object);
                INCL (obj. beFlags, StdTypes.objUsedLocalVar);
                opnd := opnd. nextOpnd
              END
            END
          ELSE
          END;

          IF (opc >= 0) THEN
            res := instr. nextResult;
            WHILE (res # NIL) DO
              IF (res. location # NIL) & (res. useList # NIL) THEN
                IF (res. location(D.SymLocation). var IS D.Object) THEN
                  obj := res. location(D.SymLocation). var(D.Object);
                  IF (obj. localTo = greg. bodyOf) & 
                     (obj. mode = D.objVar) THEN
                    INCL (obj. beFlags, StdTypes.objUsedLocalVar)
                  END
                END;
                res. location := TransformLocation (greg,
                                                  res. location(D.SymLocation))
              END;
              res := res. nextResult
            END
          END
        END;
        instr := next
      END
    END MemoryLocations;

  PROCEDURE Marker2Pos (r: D.Region);
    VAR
      i: D.Instruction;
    BEGIN
      r. pos := r. marker;
      i := r. instrList;
      WHILE (i # NIL) DO
        i. pos := i. marker;
        IF (i IS D.Region) THEN
          Marker2Pos (i(D.Region))
        END;
        i := i. nextInstr
      END
    END Marker2Pos;
  
  BEGIN
(*debug    WriteGSA.Body (greg); (* set up instruction ids for debug output *)
    Marker2Pos (greg);*)
    
    (* remove conflicts between live ranges stored in local scalar variables *)
    ResolveVarConflicts (greg);
    greg. NumberDominanceTree();       (* prepare for fast dominance tests *)
    greg. ClearInfo (noMark);         (* clear info&marker of results *)

    (* assign locations to memory references *)
    MemoryLocations (greg);
    (* assign locations to values that are created/passed in registers *)
    Region (greg);

    summary := greg. info(RegionSummary);
    AssignRegisters (summary. rf[Class.instrInt-regOff],
                     Class.prefixInt);
    AssignRegisters (summary. rf[Class.instrHuge-regOff],
                     Class.prefixHuge);
    AssignRegisters (summary. rf[Class.instrReal-regOff],
                     Class.prefixReal);
    AssignRegisters (summary. rf[Class.instrLongReal-regOff],
                     Class.prefixLongReal);
    FOR reg := 0 TO registerFiles-1 DO
      PropagateRegisters (greg, reg);
      FOR i := 0 TO rangeInfo[reg]. currRows-1 DO
        rangeInfo[reg]. res[i] := NIL
      END
    END;
    
    i := summary. rf[0]. localCount;
    IF (i < LEN (allocCounter)-1) THEN
      INC (allocCounter[i])
    ELSE
      INC (allocCounter[LEN (allocCounter)-1])
    END
  END GlobalRegion;



PROCEDURE WriteRegType* (w: TextRider.Writer; reg: SHORTINT);
  VAR
    form: SHORTINT;
    str: ARRAY 64 OF CHAR;
  BEGIN
    CASE reg OF
    | Class.instrInt: form := D.strLongInt
    | Class.instrHuge: form := D.strHugeInt
    | Class.instrReal: form := D.strReal
    | Class.instrLongReal: form := D.strLongReal
    END;
    StdTypes.BasicTypes (form, str);
    w. WriteString (str);
    w. WriteChar (" ")
  END WriteRegType;

PROCEDURE EmitVariables* (w: TextRider.Writer; greg: D.GlobalRegion;
                          vsStack: BOOLEAN);
(* Writes out a series of declarations of the variables that are used as 
   "registers" in this greg.  Also inserts variables used by a PUSHCONTEXT
   in the greg.  If `vsStack' is TRUE those variables include a local copy
   of the pointer to the current top of the stack for value array parameters.*)
   
  PROCEDURE WriteRegisters (off: SHORTINT);
    PROCEDURE WriteDeclarations (prefix: ARRAY OF CHAR; reg, off: SHORTINT);
      VAR
        i: LONGINT;
      BEGIN
        IF (greg. info(RegionSummary). rf[reg]. localCount # 0) THEN
          w. WriteLn;
          IF (off = -1) THEN
            (* declaring the variables as `register' tells the C compiler that 
               their address in never computed (directly or indirectly); 
               therefore it can assume that the variable's value is only
               accessed and modified in the current function, increasing the 
               optimization potential for the C compiler *)
            w. WriteString ("  register ")
          ELSE
            WHILE (off > 0) DO
              w. WriteString ("  ");
              DEC (off)
            END
          END;
          WriteRegType (w, reg+regOff);
          FOR i := 0 TO greg. info(RegionSummary). rf[reg]. localCount-1 DO
            IF (i # 0) THEN
              w. WriteString (", ")
            END;
            w. WriteString (prefix);
            w. WriteLInt (i, 0)
          END;
          w. WriteChar (";")
        END
      END WriteDeclarations;

    BEGIN
      WriteDeclarations (Class.prefixInt, Class.instrInt-regOff, off);
      WriteDeclarations (Class.prefixHuge, Class.instrHuge-regOff, off);
      WriteDeclarations (Class.prefixReal, Class.instrReal-regOff, off);
      WriteDeclarations (Class.prefixLongReal, Class.instrLongReal-regOff, off)
    END WriteRegisters;
  
  PROCEDURE WriteAssignments (aprefix0, aprefix1: ARRAY OF CHAR);
    PROCEDURE WriteList (prefix: ARRAY OF CHAR; reg: SHORTINT);
      VAR
        i: LONGINT;
      BEGIN
        FOR i := 0 TO greg. info(RegionSummary). rf[reg]. localCount-1 DO
          w. WriteString (" \");
          w. WriteLn;
          w. WriteString (aprefix0);
          w. WriteString (prefix);
          w. WriteLInt (i, 0);
          w. WriteString (" = ");
          w. WriteString (aprefix1);
          w. WriteString (prefix);
          w. WriteLInt (i, 0);
          w. WriteChar (";")
        END
      END WriteList;
    
    BEGIN
      WriteList (Class.prefixInt, Class.instrInt-regOff);
      WriteList (Class.prefixHuge, Class.instrHuge-regOff);
      WriteList (Class.prefixReal, Class.instrReal-regOff);
      WriteList (Class.prefixLongReal, Class.instrLongReal-regOff)
    END WriteAssignments;
  
  BEGIN
    WriteRegisters (-1);
    
    IF (Class.instrSpecialDecl IN greg. flags) THEN
      (* Classify.Region has detected some special procedure call in need of
         additional declaration; currently only one such procedure exists, so
         we can emit declarations for PUSHCONTEXT without further checking *)
      w. WriteLn;
      w. WriteString ("  _ExecutionContextDesc _local_context;");
      w. WriteLn;
      w. WriteString ("  struct {");
      WriteRegisters (2);
      IF vsStack THEN
        w. WriteLn;
        w. WriteString ("    char* top_vs;")
      END;
      w. WriteLn;
      w. WriteString ("  } _local_reg;");
      
      (* while we are at it we can #define the code to save and restore the
         registers, too; the defines are simply a sequence of assignments
         to/from _local_regs *)
      w. WriteLn;
      w. WriteString ("#undef _SAVE_RVARS");
      w. WriteLn;
      w. WriteString ("#define _SAVE_RVARS");
      WriteAssignments ("_local_reg.", "");
      IF vsStack THEN
        w. WriteString (" \");
        w. WriteLn;
        w. WriteString ("_local_reg.top_vs = _top_vs;")
      END;
      w. WriteLn;
      w. WriteString ("#undef _RESTORE_RVARS");
      w. WriteLn;
      w. WriteString ("#define _RESTORE_RVARS");
      WriteAssignments ("", "_local_reg.");
      IF vsStack THEN
        w. WriteString (" \");
        w. WriteLn;
        w. WriteString ("_top_vs = _local_reg.top_vs;")
      END;
    END
  END EmitVariables;

PROCEDURE WriteStats*;  (* debug *)
  VAR
    numAlloc, numGreg, max, i: LONGINT;
  BEGIN
    numAlloc := 0; numGreg := 0; max := 0;
    FOR i := 0 TO LEN (allocCounter)-1 DO
      INC (numGreg, allocCounter[i]);
      INC (numAlloc, allocCounter[i]*i);
      IF (allocCounter[i] # 0) THEN
        max := i
      END
    END;
    
    Out.String ("statistic of allocated integer registers:"); Out.Ln;
    Out.LongInt (numAlloc, 0); Out.String (" registers allocated in ");
    Out.LongInt (numGreg, 0); Out.String (" global regions"); Out.Ln;
    Out.Real (numAlloc / numGreg, 0, 4); Out.String (" registers per greg"); 
    Out.Ln;
    Out.String ("#reg : #regions"); Out.Ln;
    FOR i := 0 TO max DO
      IF (i = LEN (allocCounter)-1) THEN
        Out.String (">="); Out.LongInt (i, 3)
      ELSE
        Out.LongInt (i, 5)
      END;
      Out.String (": ");
      Out.LongInt (allocCounter[i], 0);
      Out.Ln
    END
  END WriteStats;

BEGIN
  NEW (undefResult);
  NEW (copyMarker);
  ClearVariables
END Allocate.
