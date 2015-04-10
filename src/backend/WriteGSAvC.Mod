(* 	$Id: WriteGSAvC.Mod,v 1.18 1999/07/16 17:02:27 acken Exp $	 *)
MODULE WriteGSAvC;  (* Copyright (C) 1995-1999  Michael van Acken *)

IMPORT
  Strings, IntStr, Out, ParamOptions, C := Classify,
  D := Data, Opc := Opcode, Allocate, ControlFlow, WriteSymbols;

CONST
  mark* = MIN(LONGINT);
  

VAR
  writeGSA-: ParamOptions.BooleanOption; 
  writeLoc: ParamOptions.BooleanOption; 
  writeQualNames-: ParamOptions.BooleanOption;
  (* if this is set, all names refering to objects or structs are written
     as qualified identifiers, i.e. they include the module and procedure 
     names; otherwise just the name is written; this option is _very_ helpful
     if you want to tell one x apart from the other *)
     
VAR
  mod: D.Object;
  (* module which contains the written code fragments *)

  
PROCEDURE Id (off: LONGINT; marker: LONGINT; pos: LONGINT);
  BEGIN
    Out.Ln;
    INC (off, 2);                       (* make room for marker *)
    IF (pos = mark) THEN
      Out.String ("[XXX] ");  (* 6 chars --> 3 indent levels *)
      (* adjust indentation level to take mark into account *)
      IF (off >= 3) THEN
        DEC (off, 3)
      ELSE
        off := 0
      END
    END;
    WHILE (off > 0) DO
      Out.String ("  ");
      DEC (off)
    END;
    Out.Char ("(");
    Out.LongInt (marker, 0);
    Out.String (") ")
  END Id;

PROCEDURE Name (a: D.Addressable; VAR str: ARRAY OF CHAR);
  VAR
    obj: D.Addressable;
  BEGIN
    obj := a;
    WITH obj: D.Object DO
      IF (obj. name[0] = "$") THEN  (* pseudo-variables *)
        COPY (obj. name^, str)
      ELSIF (obj. localTo = NIL) THEN  (* formal parameter of procedure type *)
        COPY (obj. name^, str);
        Strings.Insert ("<fpar>", 0, str)
      ELSIF (obj. localTo IS D.Struct) THEN  (* record field or tb proc *)
        Name (obj. localTo, str);
        IF (obj. mode = D.objField) THEN
          Strings.Insert ("<field>", 0, str)
        ELSE
          Strings.Insert ("<tb_proc>", 0, str)
        END;
        Strings.Append (".", str);
        Strings.Append (obj. name^, str)
      ELSIF ~writeQualNames. true OR (obj. mode = D.objModule) THEN
        COPY (obj. name^, str)
      ELSE
        Name (obj. localTo, str);
        Strings.Append (".", str);
        Strings.Append (obj. name^, str)
      END;
    | obj: D.Struct DO
      IF (obj. obj # NIL) THEN  (* named type *)
        Name (obj. obj, str)
      ELSE
        COPY ("<anon_struct>", str)
      END
    END
  END Name;

PROCEDURE Argument (i: D.Info; VAR str: ARRAY OF CHAR);
  VAR
    str0: ARRAY 256 OF CHAR;
    counter: INTEGER;
    res: D.Result;
    i0: D.Info;
  BEGIN
    i0 := i;
    WITH i0: D.Addressable DO
      Name (i0, str)
    | i0: D.Const DO
      WriteSymbols.Const (i0, str)
    | i0: D.Instruction DO
      COPY ("()", str);
      IntStr.IntToStr (i0. marker, str0);
      IF (i0. nextResult # NIL) THEN
        Strings.Insert (".0", 1, str)
      END;
      Strings.Insert (str0, 1, str)
    | i0: D.Result DO
      Argument (i0. instr, str);
      Strings.Delete (str, Strings.Length (str)-3, 2);
      counter := 0;
      res := i0. instr;
      WHILE (res # i0) DO
        INC (counter);
        res := res. nextResult
      END;
      IntStr.IntToStr (counter, str0);
      Strings.Insert (".", 0, str0);
      Strings.Insert (str0, Strings.Length (str)-1, str)
    END
  END Argument;

PROCEDURE Location (loc: D.Location; VAR str: ARRAY OF CHAR);
  VAR
    s: ARRAY 256 OF CHAR;
  BEGIN
    IF (loc = NIL) THEN
      COPY ("_", str)
    ELSE
      WITH loc: D.SymLocation DO
        Argument (loc. var, str);
        CASE loc. attrib OF
        | D.symLocAddress: s := "/adr"
        | D.symLocTypeTag: s := "/tag"
        | D.symLocObject: s := ""
        ELSE
          IntStr.IntToStr (loc. attrib, s);
          Strings.Insert ("/len", 0, s)
        END;
        Strings.Append (s, str)
      | loc: Allocate.Location DO
        IF writeLoc. true THEN
          COPY ('"', str);
          Strings.Append (loc. value^, str);
          Strings.Append ('"', str)
        ELSE
          COPY ("*", str)
        END
      ELSE
        COPY ("??", str)
      END
    END
  END Location;

PROCEDURE Subclass (scode: INTEGER; VAR str: ARRAY OF CHAR);
  VAR 
    s: ARRAY 16 OF CHAR;
  BEGIN
    CASE scode OF
    | Opc.subclS  : s := "s"
    | Opc.subclSU : s := "su"
    | Opc.subclI  : s := "i"
    | Opc.subclIU : s := "iu"
    | Opc.subclL  : s := "l"
    | Opc.subclLU : s := "lu"
    | Opc.subclLL : s := "ll"
    | Opc.subclLLU: s := "llu"
    | Opc.subclR  : s := "r"
    | Opc.subclD  : s := "d"
    | Opc.subclStr: s := "str"
    | Opc.subclLStr: s := "lstr"
    ELSE
      IntStr.IntToStr (scode, s);
      Strings.Insert ("?", 0, s);
      Strings.Append ("?", s)
    END;
    COPY (s, str)
  END Subclass;

PROCEDURE Class* (ccode: INTEGER; VAR str: ARRAY OF CHAR);
  VAR
    c: ARRAY 16 OF CHAR;
  BEGIN
    CASE ccode OF
    | 0: c := "special"
    | Opc.classAccess: c := "access"
    | Opc.classUpdate: c := "update"
    | Opc.classGuard: c := "guard"
    | Opc.classMerge: c := "merge"
    | Opc.classTrap: c := "trap"
    | Opc.classConv: c := "conv"
    | Opc.classAdd: c := "add"
    | Opc.classSub: c := "sub"
    | Opc.classMult: c := "mult"
    | Opc.classDivReal: c := "divr"
    | Opc.classDivInt: c := "divi"
    | Opc.classMod: c := "mod"
    | Opc.classNeg: c := "neg"
    | Opc.classInter: c := "inter"
    | Opc.classSymDiff: c := "symdiff"
    | Opc.classUnion: c := "union"
    | Opc.classDiff: c := "diff"
    | Opc.classCompl: c := "compl"
    | Opc.classBitSet: c := "bitset"
    | Opc.classBitClear: c := "bitclear"
    | Opc.classBitRange: c := "bitrange"
    | Opc.classBitTest: c := "bittest"
    | Opc.classNot: c := "not"
    | Opc.classAbs: c := "abs"
    | Opc.classAsh: c := "ash"
    | Opc.classCap: c := "cap"
    | Opc.classOdd: c := "odd"
    | Opc.classLsh: c := "lsh"
    | Opc.classRot: c := "rot"
    | Opc.classEql: c := "eql"
    | Opc.classNeq: c := "neq"
    | Opc.classLss: c := "lss"
    | Opc.classLeq: c := "leq"
    | Opc.classGtr: c := "gtr"
    | Opc.classGeq: c := "geq"
    END;
    COPY (c, str)
  END Class;

PROCEDURE Opcode* (opcode: INTEGER; VAR str: ARRAY OF CHAR);
  PROCEDURE Operator (opcode: INTEGER; VAR str: ARRAY OF CHAR);
    VAR
      c, s: ARRAY 16 OF CHAR;
    BEGIN
      Class (opcode DIV Opc.sizeClass, c);
      Subclass (opcode MOD Opc.sizeClass, s);
      COPY (c, str);
      Strings.Append (s, str)
    END Operator;
  
  PROCEDURE AccessSubclass (opcode: INTEGER; VAR str: ARRAY OF CHAR);
    VAR
      s: ARRAY 16 OF CHAR;
    BEGIN
      CASE opcode MOD Opc.sizeClass OF
      | Opc.subclField   : s := "field"
      | Opc.subclElement : s := "element"
      | Opc.subclHeap    : s := "heap"
      | Opc.subclNonlocal: s := "nonlocal"
      | Opc.subclVarParam: s := "var-param"
      | Opc.subclMem     : s := "mem"
      ELSE
        IntStr.IntToStr (opcode MOD Opc.sizeClass, s);
        Strings.Insert ("?", 0, s);
        Strings.Append ("?", s)
      END;
      COPY (s, str)
    END AccessSubclass;
  
  BEGIN
    CASE opcode OF
    (* special codes *)
    | Opc.enter        : COPY ("enter", str)
    | Opc.exit         : COPY ("exit", str)
    | Opc.adr          : COPY ("adr", str)
    | Opc.copy         : COPY ("copy", str)
    | Opc.gate         : COPY ("gate", str)
    | Opc.boundIndex   : COPY ("bound-index", str)
    | Opc.boundRange   : COPY ("bound-range", str)
    | Opc.call         : COPY ("call", str)
    | Opc.arrayLength  : COPY ("array-length", str)
    | Opc.typeTag      : COPY ("type-tag", str)
    | Opc.tbProcAdr    : COPY ("tb-proc-adr", str)
    | Opc.typeTest     : COPY ("type-test", str)
    | Opc.typeGuard    : COPY ("type-guard", str)
    | Opc.typeAssert   : COPY ("type-assert", str)
    | Opc.bit          : COPY ("bit", str)
    | Opc.typeCast     : COPY ("type-cast", str)
    | Opc.stringCopy   : COPY ("string-copy", str)
    | Opc.structCopy   : COPY ("struct-copy", str)
    | Opc.new          : COPY ("new", str)
    | Opc.newBlock     : COPY ("new-block", str)
    | Opc.move         : COPY ("move", str)
    | Opc.createStore  : COPY ("create-store", str)
    | Opc.deleteStore  : COPY ("delete-store", str)
    | Opc.zero         : COPY ("zero", str)
    (* access and update *)
    | Opc.classAccess*Opc.sizeClass..(Opc.classAccess+1)*Opc.sizeClass-1:
      AccessSubclass (opcode, str);
      Strings.Insert ("access-", 0, str) 
    | Opc.classUpdate*Opc.sizeClass..(Opc.classUpdate+1)*Opc.sizeClass-1:
      AccessSubclass (opcode, str);
      Strings.Insert ("update-", 0, str) 
    (* operators *)
    | Opc.classConv*Opc.sizeClass..(Opc.classGeq+1)*Opc.sizeClass-1:
      Operator (opcode, str)
    (* region codes *)
    | Opc.guardTrue : COPY ("if-true:", str)
    | Opc.guardFalse: COPY ("if-false:", str)
    | Opc.guardGreg : COPY ("greg:", str)
    | Opc.guardCase : COPY ("if-member:", str)
    | Opc.mergeIf   : COPY ("merge-if:", str)
    | Opc.mergeCond : COPY ("merge-cond:", str)
    | Opc.mergeLoop : COPY ("merge-loop:", str)
    | Opc.mergeCase : COPY ("merge-case:", str)
    (* traps *)
    | Opc.trapReturn: COPY ("trap-return", str)
    | Opc.trapCase  : COPY ("trap-case", str)
    | Opc.trapAssert: COPY ("trap-assert", str)
    | Opc.trapHalt  : COPY ("trap-halt", str)
    | Opc.trapWith  : COPY ("trap-with", str)
    (* pseudo opcodes *)
    | ControlFlow.jump         : COPY ("jump", str)
    | ControlFlow.branchOnFalse: COPY ("branch-on-false", str)
    | ControlFlow.branchOnTrue : COPY ("branch-on-true", str)
    | ControlFlow.assignGates  : COPY ("assign-gates", str)
    | ControlFlow.endOfGreg    : COPY ("end-of-greg", str)
    ELSE
      IntStr.IntToStr (opcode, str);
      Strings.Insert ("?opc", 0, str);
      Strings.Append ("?", str)
    END
  END Opcode;


PROCEDURE WrArgument* (i: D.Info);
  VAR
    str: ARRAY 256 OF CHAR;
  BEGIN
    Argument (i, str);
    Out.String (str)
  END WrArgument;

PROCEDURE WrLocation (loc: D.Location);
  VAR
    str: ARRAY 256 OF CHAR;
  BEGIN
    Location (loc, str);
    Out.String (str)
  END WrLocation;

PROCEDURE WrSubclass (opc: INTEGER);
  VAR
    str: ARRAY 8 OF CHAR;
  BEGIN
    Subclass (opc, str);
    Out.String (str)
  END WrSubclass;
  
PROCEDURE WrOpcode* (opc: INTEGER);
  VAR
    str: ARRAY 256 OF CHAR;
  BEGIN
    Opcode (opc, str);
    Out.String (str)
  END WrOpcode;






PROCEDURE WrOperands (instr: D.Instruction);
  VAR
    opnd: D.Opnd;
  BEGIN
    opnd := instr. opndList;
    WHILE (opnd # NIL) DO
      IF (opnd = instr. opndList) THEN
        Out.String (" ")
      ELSE
        Out.String (", ")
      END;
      IF (opnd. pos = mark) THEN
        Out.String ("[XXX]")
      END;
      IF (instr. opcode DIV Opc.sizeClass = Opc.classConv) &
         (opnd = instr. opndList) THEN
        (* write first operand of conv instruction as type *)
        Out.String ("<type ");
        WrSubclass (SHORT (opnd. arg(D.Const). int));
        Out.Char (">")
      ELSIF (instr. opcode = Opc.guardCase) & (opnd # instr. opndList) THEN
        Out.LongInt (opnd. arg(D.Const). int, 0);
        Out.String ("..");
        Out.LongInt (opnd. arg(D.Const). int2, 0)
      ELSE
        WrArgument (opnd. arg)
      END;
      IF (opnd. location # NIL) THEN
        Out.Char (":");
        WrLocation (opnd. location)
      END;
      opnd := opnd. nextOpnd
    END
  END WrOperands;

PROCEDURE WrResults (instr: D.Instruction);
  VAR
    res: D.Result;
    noResult: BOOLEAN;
    resultCount: INTEGER;
  BEGIN
    noResult := TRUE;
    IF (instr. location # NIL) THEN
      (* the instruction is the rhs of an assignment: emit variable name;
         IMPORTANT: this field is only available set for debugging purposes,
         usually it's NIL;  the back-end must not use this information! *)
      WrLocation (instr. location);
      noResult := FALSE
    END;
    res := instr. nextResult;
    resultCount := 1;
    WHILE (res # NIL) DO
      IF ~noResult THEN
        Out.String (", ")
      END;
      IF (res. location = NIL) THEN
        Out.String ("res.");
        Out.Int (resultCount, 0)
      ELSE
        WrLocation (res. location)
      END;
      noResult := FALSE;
      INC (resultCount);
      res := res. nextResult
    END;
    IF ~noResult THEN
      Out.String (" := ")
    END
  END WrResults;

PROCEDURE WrFlags (instr: D.Instruction);
  BEGIN
    IF (instr. flags # {}) THEN
      Out.String ("  {");
      IF (D.instrNotDead IN instr. flags) THEN
        Out.String (" notDead")
      END;
      IF (D.instrIsDisabled IN instr. flags) THEN
        Out.String (" isDisabled")
      END;
      IF (D.instrCheckOverflow IN instr. flags) THEN
        Out.String (" checkOverflow")
      END;
      IF (D.instrCheckNil IN instr. flags) THEN
        Out.String (" checkNil")
      END;
      IF (D.instrCheckDiv IN instr. flags) THEN
        Out.String (" checkDiv")
      END;
      IF (D.instrInitialize IN instr. flags) THEN
        Out.String (" initialize")
      END;
      IF (D.instrStackCheck IN instr. flags) THEN
        Out.String (" stackCheck")
      END;
      IF (D.instrUniqueResult IN instr. flags) THEN
        Out.String (" uniqueResult")
      END;
      IF (D.instrGuardFor IN instr. flags) THEN
        Out.String (" guardFor")
      END;
      IF (D.instrPoisonHeap IN instr. flags) THEN
        Out.String (" poisonHeap")
      END;
      IF (C.instrNoOutput IN instr. flags) THEN
        Out.String (" noOutput")
      END;
      IF (C.instrVoid IN instr. flags) THEN
        Out.String (" void")
      END;
      IF (C.instrInt IN instr. flags) THEN
        Out.String (" int")
      END;
      IF (C.instrHuge IN instr. flags) THEN
        Out.String (" huge")
      END;
      IF (C.instrReal IN instr. flags) THEN
        Out.String (" real")
      END;
      IF (C.instrLongReal IN instr. flags) THEN
        Out.String (" longreal")
      END;
      Out.String (" }")
    END
  END WrFlags;

PROCEDURE WrInstr (instr: D.Instruction; off: INTEGER);
  BEGIN
    Id (off, instr. marker, instr. pos);
    WrResults (instr);
    WrOpcode (instr. opcode);
    WrOperands (instr);
    WrFlags (instr);
    IF (instr IS D.Region) THEN
      (* emit instruction list *)
      instr := instr(D.Region). instrList;          
      WHILE (instr # NIL) DO
        WrInstr (instr, off+1);
        instr := instr. nextInstr
      END
    END
  END WrInstr;

PROCEDURE SetMarkers (greg: D.Region);
  VAR
    counter: LONGINT;
    
  PROCEDURE MarkInstr (instr: D.Instruction);
    BEGIN
      instr. marker := counter;
      INC (counter);
      IF (instr IS D.Region) THEN
        instr := instr(D.Region). instrList;
        WHILE (instr # NIL) DO
          MarkInstr (instr);
          instr := instr. nextInstr
        END
      END
    END MarkInstr;
  
  BEGIN
    counter := 1;
    MarkInstr (greg)    
  END SetMarkers;


PROCEDURE Body* (greg: D.GlobalRegion);
(* Writes GSA code of `greg' to stdout.  Instructions and operands marked with 
   the position `mark' are marked with [XXX].  *)
  BEGIN
    IF writeGSA. true THEN
      mod := greg. bodyOf. Module();
      SetMarkers (greg);
      IF (greg. bodyOf. mode = D.objModule) THEN
        Out.String ("module body: ")
      ELSE
        Out.String ("procedure "); 
        WrArgument (greg. bodyOf);
        Out.Char (":")
      END;
      WrInstr (greg, 0);
      Out.Ln;
      mod := NIL  (* get rid of unused reference to heap *)
    END
  END Body;

PROCEDURE MW* (n: D.Node);
(* Mark operand or instruction `n' and write the global region it belongs to.*)
  VAR
    old: BOOLEAN;
  BEGIN
    ASSERT ((n IS D.Opnd) OR (n IS D.Instruction));
    WITH n: D.Opnd DO
      n. pos := mark
    | n: D.Instruction DO
      n. pos := mark
    END;
    old := writeGSA. true;
    writeGSA. Set (TRUE);
    Body (n. Greg());
    writeGSA. Set (old)
  END MW;

BEGIN
  writeGSA := ParamOptions.CreateBoolean ("writeGSAC", FALSE);
  ParamOptions.options. CmdLineOption ("--cgsa", "writeGSAC:=TRUE");
  ParamOptions.options. Add (writeGSA);
  
  writeLoc := ParamOptions.CreateBoolean ("writeLocC", FALSE);
  ParamOptions.options. CmdLineOption ("--cgsa-loc", "writeLocC:=TRUE");
  ParamOptions.options. Add (writeLoc);

  writeQualNames := ParamOptions.CreateBoolean ("writeQualNamesC", FALSE);
  ParamOptions.options. CmdLineOption ("--cgsa-qnames", "writeQualNamesC:=TRUE");
  ParamOptions.options. Add (writeQualNames)
END WriteGSAvC.
