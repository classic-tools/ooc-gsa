(*	$Id: GenStatm.Mod,v 1.51 1999/07/16 17:02:31 acken Exp $	*)
MODULE GenStatm;
(*  Translates GSA opcodes to C statements.
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
  TextRider, ParamOptions, Out, Strings, IntStr, StdPragmas,
  Config, D := Data, Opc := Opcode, Sym := SymbolTable, Attr := Attributes, 
  StdTypes, SF := SystemFlags, A := Allocate, Class := Classify, Schedule,
  ControlFlow, GenConst, GenDecl, WriteGSA := WriteGSAvC;


VAR
  writeSyncStatm: ParamOptions.BooleanOption;

VAR
  valueStack-: ParamOptions.IntegerOption;
  (* if this option has a non-negative value, then the compiler will allocate
     a memory block of the given size to hold open array value parameters of
     procedures; with a negative value the compiler will use the function
     alloca() to allocate storage for them; alloca() gets its memory from the
     standard stack, and it is automatically popped from the stack when leaving
     the function; alloca() is a BSD extension and not available for all
     compilers (gcc supports it, though)  *)
  gcflags-: ParamOptions.StringOption;


VAR
  w: TextRider.Writer;
  off: INTEGER;
  localOpenArray: BOOLEAN;
  
  
TYPE
  Assignment = RECORD
    src: D.Opnd;
    srcLoc: A.Location;
    destLoc: A.Location;
    cat: SHORTINT;
  END;
  AssignArray = POINTER TO ARRAY OF Assignment;

VAR
  assignArray: AssignArray;
  currId: LONGINT;  
  opList: ARRAY 9 OF CHAR;

PROCEDURE SetWriter* (writer: TextRider.Writer);
  BEGIN
    w := writer;
    off := 0
  END SetWriter;

PROCEDURE NewLine;
(* Write `newline' and indent for `off' levels.  *)
  VAR
    i: INTEGER;
  BEGIN
    i := off;
    w. WriteLn;
    IF WriteGSA.writeGSA. true THEN
      IF (currId < 0) THEN
        w. WriteString ("/*    */ ")
      ELSE
        w. WriteString ("/*");
        CASE currId OF
        | 0..9: w. WriteString ("   ")
        | 10..99: w. WriteString ("  ")
        | 100..999: w. WriteString (" ")
        ELSE
        END;
        w. WriteLInt (currId, 0);
        w. WriteString ("*/ ")
      END;
      currId := -1
    END;
    WHILE (i # 0) DO
      w. WriteString ("  ");
      DEC (i)
    END
  END NewLine;

PROCEDURE WriteName (obj: D.Object);
  BEGIN
    w. WriteString (obj. beInfo(SF.Info). name^)
  END WriteName;

PROCEDURE GetLocation (u: D.Node): A.Location;
  VAR
    v: D.Node;
    loc: A.Location;
  BEGIN
    v := u;
    WITH v: D.Opnd DO
      loc := v. location(A.Location)
    | v: D.Instruction DO
      IF (v. opcode DIV Opc.sizeClass = Opc.classAccess) &
         (Class.instrVoid IN v. flags) THEN
        (* access instruction for a structured value; use the address for the
           actual location *)
        loc := GetLocation (v. opndList. nextOpnd. arg)
      ELSE
        loc := v. location(A.Location)
      END
    | v: D.Result DO
      loc := v. location(A.Location)
    END;
    RETURN loc
  END GetLocation;

PROCEDURE WriteLocation (u: D.Node);
  VAR
    loc: A.Location;
  BEGIN
    loc := GetLocation (u);
    w. WriteString (loc. value^)
  END WriteLocation;

PROCEDURE WriteArg (opnd: D.Opnd);
  VAR
    arg: D.Usable;
  BEGIN
    arg := opnd. arg;
    WITH arg: D.Const DO
      GenConst.Const (w, arg, NIL)
    | arg: D.Result DO
      WriteLocation (arg)
    | arg: D.Object DO
      w. WriteString (arg. beInfo(SF.Info). name^)
    END
  END WriteArg;

PROCEDURE WriteNthArg (index: INTEGER; instr: D.Instruction);
  BEGIN
    WriteArg (instr. NthOperand (index))
  END WriteNthArg;

PROCEDURE WriteResultCast (instr: D.Instruction; unsigned: BOOLEAN);
  BEGIN
    IF (Class.instrInt IN instr. flags) THEN
      GenDecl.WriteScalarCast (w, D.struct[D.strLongInt], unsigned, FALSE, FALSE)
    ELSE
      GenDecl.WriteScalarCast (w, D.struct[D.strHugeInt], unsigned, FALSE, FALSE)
    END
  END WriteResultCast;


PROCEDURE WritePos (pos: LONGINT);
  BEGIN
    w. WriteString ("_P(");
    w. WriteLInt (pos, 0);
    w. WriteString (")")
  END WritePos;

PROCEDURE WriteDyOp (instr: D.Instruction;
                     op: ARRAY OF CHAR; opnd0, opnd1: INTEGER);
  CONST
    standardAssign = 0; shortAssign = 1; postIncr = 2; postDecr = 3;
  VAR
    style: SHORTINT;
    
  PROCEDURE OpStyle(): SHORTINT;
    VAR
      pos: INTEGER;
      arg: D.Usable;
      loc0, loc1: A.Location;
      found: BOOLEAN;
    
    PROCEDURE Const (val: SHORTINT): BOOLEAN;
      BEGIN
        RETURN (arg(D.Const). int = val)
      END Const;
    
    BEGIN
      Strings.FindNext (op, opList, 0, found, pos);
      arg := instr. NthArgument (opnd0);
      IF found & (arg IS D.Result) THEN
        loc0 := GetLocation (instr);
        loc1 := GetLocation (arg);
        IF (loc0. value^ = loc1. value^) THEN
          arg := instr. NthArgument (opnd1);
          IF (arg IS D.Const) & 
             Sym.TypeInGroup (arg(D.Const). type, D.grpInteger) THEN
            IF (op[0] = "+") & Const (1) OR (op[0] = "-") & Const (-1) THEN
              RETURN postIncr
            ELSIF (op[0] = "-") & Const (1) OR (op[0] = "+") & Const (-1) THEN
              RETURN postDecr
            END
          END;
          RETURN shortAssign
        END
      END;
      RETURN standardAssign
    END OpStyle;
  
  BEGIN
    NewLine;
    WriteLocation (instr);
    style := OpStyle();
    CASE style OF
    | standardAssign:
      w. WriteString (" = ");
      WriteNthArg (opnd0, instr);
      w. WriteChar (" ");
      w. WriteString (op);
      w. WriteChar (" ");
      WriteNthArg (opnd1, instr)
    | shortAssign:
      w. WriteChar (" ");
      w. WriteString (op);
      w. WriteString ("= ");
      WriteNthArg (opnd1, instr);
    | postIncr:
      w. WriteString ("++")
    | postDecr:
      w. WriteString ("--")
    END;
    w. WriteChar (";")
  END WriteDyOp;

PROCEDURE WriteMonOp (instr: D.Instruction; op: ARRAY OF CHAR; opnd: INTEGER);
  BEGIN
    NewLine;
    WriteLocation (instr);
    w. WriteString (" = ");
    IF (op[0] # 0X) THEN
      w. WriteString (op);
      w. WriteChar (" ")
    END;
    WriteNthArg (opnd, instr);
    w. WriteChar (";")
  END WriteMonOp;

PROCEDURE WriteDyCall (instr: D.Instruction;
                       fct: ARRAY OF CHAR; opnd0, opnd1: INTEGER);
  BEGIN
    NewLine;
    IF ~(Class.instrVoid IN instr. flags) THEN
      WriteLocation (instr);
      w. WriteString (" = ")
    END;
    w. WriteString (fct);
    w. WriteChar ("(");
    WriteNthArg (opnd0, instr);
    w. WriteString (", ");
    WriteNthArg (opnd1, instr);
    w. WriteString (");")
  END WriteDyCall;

PROCEDURE WriteMonCall (instr: D.Instruction;
                        fct: ARRAY OF CHAR; opnd: INTEGER);
  BEGIN
    NewLine;
    IF ~(Class.instrVoid IN instr. flags) THEN
      WriteLocation (instr);
      w. WriteString (" = ")
    END;
    w. WriteString (fct);
    w. WriteChar ("(");
    WriteNthArg (opnd, instr);
    w. WriteString (");")
  END WriteMonCall;


PROCEDURE ForceToMem (greg: D.GlobalRegion; opnd: D.Opnd);
(* Forces argument of `opnd' into its memory location.
   pre: `opnd' is associated with a location of type `D.SymLocation' *)
  VAR
    cloc: D.Location;
    loc: D.SymLocation;
    str: ARRAY 512 OF CHAR;
    pos: INTEGER;
    found: BOOLEAN;

  PROCEDURE SymbolicValue (l: D.Location): BOOLEAN;
  (* Returns TRUE iff `l' describes a real variable.
     pre: l # NIL  *)
    BEGIN
      WITH l: D.SymLocation DO
        IF (l. var IS D.Struct) THEN
          (* operand is a `Struct' value, describing an assignment to a heap
             object *)
          RETURN  TRUE
        ELSIF (l. attrib # D.symLocObject) THEN
          (* location denotes a static attribute (address, tag, or length) of a
             variable, therefore it doesn't have to be moved to memory *)
          RETURN TRUE
        ELSIF (l. var(D.Object). name[0] = "$") THEN
          (* argument denotes a value of one of the pseudo variables $mem,
             $store, $result, etc *)
          RETURN TRUE
        ELSE
          RETURN FALSE
        END
      ELSE
        RETURN TRUE
      END
    END SymbolicValue;

  PROCEDURE NoChange (l: D.SymLocation; arg: D.Usable): BOOLEAN;
  (* Returns TRUE if `l' is a variable whose content are read with the access
     instruction `arg'.  This means that the value in `l' doesn't have to 
     be updated.  *)
    VAR
      opc: INTEGER;
    BEGIN
      WITH arg: D.Instruction DO
        opc := arg. opcode;
        IF (opc = Opc.accessNonlocal) OR (opc = Opc.accessVarParam) THEN
          RETURN (arg. opndList. arg = l. var)
        ELSE
          RETURN FALSE
        END
      ELSE
        RETURN FALSE
      END
    END NoChange;
  
  BEGIN
    IF ~((opnd. arg IS D.Object) OR
         SymbolicValue (opnd. location) OR
         Sym.TypeInGroup (opnd. OpndType(), D.grpStructured) OR
         NoChange (opnd. location(D.SymLocation), opnd. arg)) THEN
      (* ignore undefined values, pseudo values or structured variables *)
      loc := A.GetLocation (opnd);
      IF (loc. var(D.Object). localTo # greg. bodyOf) THEN
        cloc := A.AccessNonlocal (greg, loc. var(D.Object), "")
      ELSE
        cloc := A.TransformLocation (greg, loc)
      END;
      IF ~(opnd. arg IS D.Result) OR
         ~(opnd. arg(D.Result). location IS A.Location) OR
         (cloc(A.Location). value^ #
          opnd. arg(D.Result). location(A.Location). value^) THEN
        NewLine;
        (* strip cast from location string *)
        Strings.FindNext (")", cloc(A.Location). value^, 0, found, pos);
        IF ~found THEN
          w. WriteString (cloc(A.Location). value^)
        ELSE
          Strings.Extract (cloc(A.Location). value^, pos+1,
                           MAX (INTEGER), str);
          w. WriteString (str)
        END;
        w. WriteString (" = ");
        GenDecl.WriteScalarCast (w, loc. var(D.Object). type,
                                 FALSE, FALSE, FALSE);
        WriteArg (opnd);
        w. WriteChar (";")
      END
    END
  END ForceToMem;

PROCEDURE ForceListToMem (greg: D.GlobalRegion; opndList: D.Opnd);
(* Writes the operands of a collect or an exit instruction to their dedicated
   memory locations.
   pre: Every operand in `opndList' is associated with a location of type
     `D.SymLocation'.  *)
  BEGIN
    WHILE (opndList # NIL) DO
      ForceToMem (greg, opndList);
      opndList := opndList. nextOpnd
    END
  END ForceListToMem;
  
PROCEDURE CollectToMem (greg: D.GlobalRegion; instr: D.Instruction);
(* Force the values of any local variables into memory as required by the 
   opernand list of `instr'.  Called for instructions that take arguments from
   memory, exept for procedure calls.  *)
  VAR
    memOpnd: D.Opnd;
  BEGIN
    memOpnd := instr. GetOperand (Sym.mem, D.symLocObject);
    IF (memOpnd # NIL) THEN
      ForceListToMem (greg, memOpnd)
    END
  END CollectToMem;

PROCEDURE CastFromScalarType (opnd: D.Opnd): D.Struct;
  VAR
    type: D.Struct;
  BEGIN
    WHILE (opnd. arg IS D.Instruction) &
          (opnd. arg(D.Instruction). opcode = Opc.typeCast) DO
      opnd := opnd. arg(D.Instruction). opndList
    END;
    type := opnd. OpndType();
    IF Sym.TypeInGroup (type, D.grpStructured) OR
       Sym.TypeInGroup (type, D.grpStringConst) THEN
      RETURN NIL
    ELSE
      RETURN type
    END
  END CastFromScalarType;

  
PROCEDURE ExitInstr (exit: D.Instruction);
  VAR
    opnd, result: D.Opnd;
    obj: D.Object;
    empty: BOOLEAN;
  BEGIN
    empty := TRUE;
    
    (* force side-effects into their destination locations *)
    ForceListToMem (exit. Greg(), exit. opndList);

    IF localOpenArray & (valueStack. value >= 0) THEN
      (* pop all local copies of value parameters from stack *)
      NewLine;
      w. WriteString ("_top_vs = _old_top_vs;");
      empty := FALSE
    END;

    (* determine result value and build return instruction *)
    result := NIL;
    opnd := exit. opndList;
    WHILE (opnd # NIL) DO
      IF (opnd. location(D.SymLocation). var IS D.Object) THEN
        obj := opnd. location(D.SymLocation). var(D.Object);
        IF (obj. name^ = "$result") THEN
          result := opnd
        END
      END;
      opnd := opnd. nextOpnd
    END;
    IF (result # NIL) & ~(result. arg IS D.Object) THEN
      (* skip return if `result' argument is an undefined value *)
      NewLine;
      w. WriteString ("return ");
      GenDecl.WriteScalarCast (w, result. OpndType(), FALSE, FALSE, FALSE);
      WriteArg (result);
      w. WriteChar (";");
      empty := FALSE
    END;
    
    (* make sure that it'll never happen that exit is labeled but doesn't emit
       any code; otherwise the C compiler might complain about a label at the
       end of a compound statement *)
    IF empty & (Class.instrJumpTarget IN exit. flags) THEN
      NewLine;
      w. WriteChar (";")
    END
  END ExitInstr;

PROCEDURE SpecialCallInstr (instr: D.Instruction);
(* The procedure call activates a "special code" procedure.  Unless this case
   has been handled by one of the previous step we have to insert dedicated 
   code instead of the call.  For oo2c only PUSHCONTEXT has to be handled 
   here.  *)
  BEGIN
    (* configure and Allocate.EmitVariables have done most of the job for us;
       just put the pieces together to create the PUSHCONTEXT instruction *)
    w. WriteLn;
    w. WriteString ("#define _SOURCE_PTR ");
    WriteArg (instr. NthOperand (4));
    w. WriteLn;
    w. WriteString ('#include "__pushcontext.h"');
    w. WriteLn;
    w. WriteString ("#undef _SOURCE_PTR ")
  END SpecialCallInstr;

PROCEDURE CheckNil (instr: D.Instruction; adr: INTEGER);
  VAR
    arg: D.Usable;
    use: D.Opnd;
    needCheck: BOOLEAN;
    n, m: INTEGER;
  BEGIN
    IF (D.instrCheckNil IN instr. flags) THEN
      arg := instr. NthArgument (adr);
      needCheck := TRUE;
      use := arg. useList;
      WHILE needCheck & (use # NIL) DO
        IF (use. instr # instr) & (D.instrCheckNil IN use. instr. flags) THEN
          n := use. OperandIndex();
          CASE use. instr. opcode OF
          | Opc.accessHeap, Opc.updateHeap:
            m := 1
          | Opc.typeTag, Opc.arrayLength, Opc.call:
            m := 0
          END;
          IF (n = m) & Schedule.ExecutedBefore (use. instr, instr) THEN
            (* another instruction that tests the address against NIL is
               executed beforehand, no need to test again *)
            needCheck := FALSE
          END
        END;
        use := use. nextUse
      END;
      
      IF needCheck THEN
        NewLine;
        w. WriteString ("if (!");
        WriteNthArg (adr, instr);
        w. WriteString (") _deref_of_nil(");
        WritePos (instr. pos);
        w. WriteString (");")
      END
    END
  END CheckNil;

PROCEDURE CallInstr (instr: D.Instruction);
  VAR
    procObj, adr: D.Usable;
    formalPars: D.Struct;
    fpar: D.Object;
    opnd: D.Opnd;
    first: BOOLEAN;
    einfo: GenDecl.SideEffectInfo;
    cloc: D.Location;
    i: INTEGER;
    flags: SET;

  PROCEDURE Param (opnd: D.Opnd; fpar: D.Object; attrib: INTEGER);
    BEGIN
      IF first THEN
        first := FALSE
      ELSE
        w. WriteString (", ")
      END;

      IF (attrib = D.symLocObject) OR (attrib = D.symLocAddress) THEN
        w. WriteChar ("(");
        GenDecl.Declaration (w, fpar,
          {GenDecl.doNotMark, GenDecl.ignoreMark,
           GenDecl.formalParam, GenDecl.typeExpression,
           GenDecl.ignoreOtherModule, GenDecl.ignoreUsedDecl}, 0);
        w. WriteChar (")")
      END;

      WriteArg (opnd)
    END Param;

  PROCEDURE CollectOpnds (instr: D.Instruction);
  (* Moves all operands that have to be passed in memory to their locations. *)
    VAR
      nonParam, opnd: D.Opnd;
      greg: D.GlobalRegion;
      l: D.SymLocation;
      srcType: D.Struct;
    
    PROCEDURE FormalPar (fpar, obj: D.Object): BOOLEAN;
    (* Returns TRUE iff `obj' refers to a parameter in the formal parameter 
       list `fpar' or to the receiver of the procedure `procObj'.  *)
      BEGIN
        IF (fpar = NIL) THEN
          IF (procObj IS D.Object) &
             (procObj(D.Object). mode = D.objTBProc) THEN
            (* check if `obj' refers to the receiver variable *)
            RETURN (procObj(D.Object). data = obj)
          ELSE
            RETURN FALSE
          END
        ELSIF (fpar = obj) THEN
          RETURN TRUE
        ELSE
          RETURN FormalPar (fpar. rightObj, obj)
        END
      END FormalPar;
    
    BEGIN
      greg := instr. Greg();
      nonParam := Attr.GetNonParamOpnd (instr);
      
      IF (nonParam # NIL) & (nonParam. location = NIL) THEN
        (* operands without location are passed to C-style rest parameter;
           ignore them, since all of them are passed as value *)
      ELSE
        (* here holds: `nonParam' is the first of the operands that model 
           accesses of nonlocal variables *)
        ForceListToMem (greg, nonParam)
      END;

      (* force operand of formal VAR parameter to memory (if necessary); all
         other parameters are passed as values of a C function call and don't 
         have to be handled here *)
      opnd := instr. NthOperand (3);
      WHILE (opnd # nonParam) DO
        l := A.GetLocation (opnd);
        IF (opnd. arg IS D.Instruction) &
           (opnd. arg(D.Instruction). opcode = Opc.typeCast) THEN
          srcType := CastFromScalarType (opnd);
          IF Sym.TypeInGroup (opnd. OpndType(), D.grpStructured) &
             ~Sym.TypeInGroup (srcType, D.grpStructured) THEN
            (* we got a blasted type cast from scalar to structured type as
               argument; force the casted variable into memory *)
            ForceToMem (instr. Greg(), 
                        opnd. arg(D.Instruction). opndList)
          END
        ELSIF (l # NIL) & ~FormalPar (formalPars. decl, l. var(D.Object)) THEN
          (* only stuff passed to rest parameter has a location of NIL *)
          ForceToMem (greg, opnd)
        END;
        opnd := opnd. nextOpnd;
      END
    END CollectOpnds;

  PROCEDURE PassArgument (fpar: D.Object; VAR opnd: D.Opnd);
    BEGIN
      IF ~StdTypes.PassPerReference (fpar, TRUE) THEN
        (* parameter is passed as value; put type cast around value *)
        Param (opnd, fpar, D.symLocObject)
      ELSE  (* parameter is passed as address *)
        opnd := opnd. nextOpnd;  (* skip value *)
        Param (opnd, fpar, D.symLocAddress)
      END;
      opnd := opnd. nextOpnd;

      IF (opnd # NIL) & (opnd. location # NIL) &
         (opnd. location(D.SymLocation). var = fpar) &
         (opnd. location(D.SymLocation). attrib = D.symLocTypeTag) THEN
        Param (opnd, fpar, D.symLocTypeTag);
        opnd := opnd. nextOpnd
      END;

      i := D.symLocLength0;
      WHILE (opnd # NIL) & (opnd. location # NIL) &
            (opnd. location(D.SymLocation). var = fpar) &
            (opnd. location(D.SymLocation). attrib = i) DO
        Param (opnd, fpar, opnd. location(D.SymLocation). attrib);
        INC (i);
        opnd := opnd. nextOpnd
      END
    END PassArgument;

  BEGIN
    adr := instr. opndList. arg;
    formalPars := instr. opndList. nextOpnd. arg(D.Struct);
    procObj := instr. opndList. nextOpnd. nextOpnd. arg;
    CollectOpnds (instr);
    
    (* we might be using a procedure variable; make sure that we do not get a 
       NIL value if the user required this *)
    CheckNil (instr, 0);
    
    IF (procObj IS D.Object) & 
       (D.objIsSpecialCodeProc IN procObj(D.Object). flags) THEN
      (* special code procedure; this means we have to write dedicated code
         instead of a simple procedure call *)
      SpecialCallInstr (instr);
      RETURN
    END;

    NewLine;
    IF (formalPars. base. form # D.strNone) THEN  (* function call *)
      WriteLocation (instr);
      w. WriteString (" = ");
      IF A.PtrValue (formalPars. base) THEN
        GenDecl.WriteScalarCast (w, D.struct[D.strAddress],
                                 FALSE, FALSE, FALSE);
        (*(* casting a function result of pointer type directly to int triggers
           a warning if gcc is invoked with -Wbad-function-cast *)
        w. WriteString ("(void* )")*)
      END
    END;

    IF ~(procObj IS D.Object) OR
       ~(procObj(D.Object). mode IN {D.objProc, D.objTBProc}) OR
       ~(adr IS D.Instruction) OR
       (adr(D.Instruction). opcode # Opc.adr) THEN
      (* apply type cast to procedure value *)
      w. WriteString ("((");
      IF (procObj IS D.Object) & (procObj(D.Object). mode = D.objTBProc) THEN
        GenDecl.Declaration (w, procObj(D.Object),
                       {GenDecl.typeExpression, GenDecl.ignoreUsedDecl,
                        GenDecl.doNotMark, GenDecl.ignoreMark,
                        GenDecl.ignoreOtherModule}, 0)
      ELSE
        GenDecl.TypeDeclaration (w, formalPars,
                       {GenDecl.typeExpression, GenDecl.ignoreUsedDecl,
                        GenDecl.doNotMark, GenDecl.ignoreMark,
                        GenDecl.ignoreOtherModule}, 0)
      END;
      w. WriteChar (")");
      WriteArg (instr. opndList);
      w. WriteChar (")")
    ELSE  (* use procedure name *)
      w. WriteString (procObj(D.Object). beInfo(SF.Info). name^)
    END;
    w. WriteChar ("(");

    first := TRUE;
    fpar := formalPars. decl;
    opnd := instr. NthOperand (3);

    IF (procObj IS D.Object) & (procObj(D.Object). mode = D.objTBProc) THEN
      (* pass receiver argument *)
      PassArgument (procObj(D.Object). data(D.Object), opnd);
    END;
    WHILE (fpar # NIL) & (fpar. mode # D.objRestParam) DO
      PassArgument (fpar, opnd);
      fpar := fpar. rightObj
    END;

    IF (fpar # NIL) THEN  (* rest parameter *)
      WHILE (opnd # NIL) & 
            ((opnd. location = NIL) OR
             (opnd. location(D.SymLocation). var # Sym.mem)) DO
        (* emit all arguments before the $mem parameter *)
        Param (opnd, fpar, MIN (INTEGER));
        opnd := opnd. nextOpnd
      END
    ELSIF (procObj IS D.Object) &
          (procObj(D.Object). mode IN {D.objProc, D.objTBProc}) &
          (procObj(D.Object). greg # NIL) &
          (procObj(D.Object). greg. EnterInstr() # NIL) THEN
      (* add side-effect parameters to access or update nonlocal variables  *)
      GenDecl.EnumerateSideEffects (procObj(D.Object), einfo);
      WHILE einfo. continue DO
        IF first THEN
          first := FALSE
        ELSE
          w. WriteString (", ")
        END;

        IF einfo. passPerReference THEN
          cloc := A.GetAddressValue (instr. Greg(),
                                     einfo. obj, FALSE)
        ELSE
          cloc := A.TransformLocation (
                    instr. Greg(),
                    D.CreateSymLocation (einfo. obj, einfo. attrib))
        END;

        IF (einfo. attrib = D.symLocObject) & A.PtrValue (einfo. obj. type) OR
           (einfo. attrib = D.symLocAddress) THEN
          flags := {GenDecl.doNotMark, GenDecl.ignoreMark,
                    GenDecl.sideEffectParam, GenDecl.typeExpression,
                    GenDecl.ignoreOtherModule, GenDecl.ignoreUsedDecl};
          IF einfo. passPerReference THEN
            INCL (flags, GenDecl.sideEffectReference)
          END;
          w. WriteChar ("(");
          GenDecl.Declaration (w, einfo. obj, flags, 0);
          w. WriteChar (")")
        END;
        w. WriteString (cloc(A.Location). value^);

        GenDecl.EnumerateSideEffects (NIL, einfo)
      END
    END;

    w. WriteString (");")
  END CallInstr;

PROCEDURE ArrayLength (instr: D.Instruction);
  VAR
    dim: INTEGER;
  BEGIN
    dim := SHORT (instr. opndList. nextOpnd. arg(D.Const). int);
    CheckNil (instr, 0);
    NewLine;
    WriteLocation (instr);
    w. WriteString (" = *");
    GenDecl.WriteScalarCast (w, D.struct[D.strLongInt], FALSE, TRUE, FALSE);
    w. WriteChar ("(");
    WriteNthArg (0, instr);
    w. WriteChar ("-");
    w. WriteLInt (D.struct[D.strAddress]. size+
                  (dim+1)*D.struct[D.strLongInt]. size, 0);
    w. WriteString (");")
  END ArrayLength;

PROCEDURE TBProcAddress (instr: D.Instruction);
  VAR
    proc: D.Object;
    index: LONGINT;
  BEGIN
    proc := instr. opndList. nextOpnd. nextOpnd. arg(D.Object);
    index := proc. offset;
    NewLine;
    WriteLocation (instr);
    w. WriteString (" = ");
    GenDecl.WriteScalarCast (w, D.struct[D.strAddress], FALSE, FALSE, FALSE);
    w. WriteString ("((_Type)");
    WriteNthArg (0, instr);
    w. WriteString (")->tbprocs[");
    IF (index < 0) THEN
      w. WriteString ("_TB");
      GenDecl.RegisterTBCall (proc)
    END;
    w. WriteLInt (ABS (index), 0);
    w. WriteString ("];");
  END TBProcAddress;

PROCEDURE TypeTest (instr: D.Instruction);
  BEGIN
    NewLine;
    WriteLocation (instr);
    w. WriteString (" = _type_test(");
    WriteNthArg (1, instr);
    w. WriteString (", ");
    WriteNthArg (2, instr);
    w. WriteString (", ");
    WriteNthArg (3, instr);
    w. WriteString (");")
  END TypeTest;

PROCEDURE TypeGuard (instr: D.Instruction);
  BEGIN
    (* note: if type guards are disabled, then this instruction is removed
             during the final dead code elimination; there is no need to
             test if `instrIsDisabled' is set *)
    NewLine;
    w. WriteString ("_type_guard(");
    WriteNthArg (1, instr);
    w. WriteString (", ");
    WriteNthArg (2, instr);
    w. WriteString (", ");
    WriteNthArg (3, instr);
    w. WriteString (", ");
    WritePos (instr. pos);
    w. WriteString (");")
  END TypeGuard;

PROCEDURE TypeAssertion (instr: D.Instruction);
  BEGIN
    NewLine;
    w. WriteString ("_type_assert(");
    WriteNthArg (1, instr);
    w. WriteString (", ");
    WriteNthArg (2, instr);
    w. WriteString (", ");
    WritePos (instr. pos);
    w. WriteString (");")
  END TypeAssertion;

PROCEDURE BoundInstr (instr: D.Instruction);
  VAR
    needCheck: BOOLEAN;
    index, length: D.Usable;
    use: D.Opnd;
  BEGIN  (* pre: instr. opcode = Opc.boundIndex or Opc.boundRange *)
    (* note: if type guards are disabled, then this instruction is removed
             during the final dead code elimination; there is no need to
             test if `instrIsDisabled' is set *)
             
    (* first see if a previous check did the job for use *)
    needCheck := TRUE;
    index := instr. opndList. arg;
    length := instr. opndList. nextOpnd. arg;
    use := index. useList;
    WHILE needCheck & (use # NIL) DO
      IF (use. instr. opcode = instr. opcode) &
         (use. instr. opndList. arg = index) &
         (use. instr. opndList. nextOpnd. arg = length) &
         Schedule.ExecutedBefore (use. instr, instr) THEN
        needCheck := FALSE
      END;
      use := use. nextUse
    END;
    
    IF needCheck THEN
      NewLine;
      w. WriteString ("if (");
      GenDecl.WriteScalarCast (w, D.struct[D.strLongInt], TRUE, FALSE, FALSE);
      WriteNthArg (0, instr);
      w. WriteString (" >= ");
      GenDecl.WriteScalarCast (w, D.struct[D.strLongInt], TRUE, FALSE, FALSE);
      WriteNthArg (1, instr);
      w. WriteString (") ");

      IF (instr. opcode = Opc.boundIndex) THEN
        w. WriteString ("_index_out_of_range(")
      ELSE (* (instr. opcode = Opc.boundRange) *)
        w. WriteString ("_element_out_of_range(")
      END;
      WriteNthArg (0, instr);
      w. WriteString (", ");
      WriteNthArg (1, instr);
      w. WriteString (", ");
      WritePos (instr. pos);
      w. WriteString (");")
    END
  END BoundInstr;

PROCEDURE TypeCastInstr (instr: D.Instruction);
(* Write code for type cast with scalar destination type.  *)
  VAR
    opndType: D.Struct;

  PROCEDURE WriteAddress (greg: D.GlobalRegion; u: D.Usable);
  (* Writes address of structured value.  *)
    VAR
      l: A.Location;
      loc: D.SymLocation;
      instr: D.Instruction;
    BEGIN
      WHILE (u IS D.Result) & (u(D.Result). instr. opcode = Opc.typeCast) DO
        u := u(D.Result). instr. opndList. arg
      END;

      IF (u IS D.Object) OR (u IS D.Const) THEN
        (* direct access to variable resp. constant *)
        l := A.GetAddressValue (greg, u, FALSE);
        w. WriteString (l. value^)
      ELSIF (u IS D.Result) & (u(D.Result). instr. opcode = Opc.enter) THEN
        loc := A.GetLocation (u);
        l := A.GetAddressValue (greg, loc. var, FALSE);
        w. WriteString (l. value^)
      ELSE  (* value is result of an access instruction *)
        instr := u(D.Result). instr;
        IF (instr. opcode = Opc.accessMem) THEN
          WriteNthArg (0, instr)
        ELSE
          WriteNthArg (1, instr)
        END
      END
    END WriteAddress;

  BEGIN
    NewLine;
    w. WriteChar ("{");
    INC (off);

    opndType := instr. opndList. OpndType();
    IF Sym.TypeInGroup (opndType, D.grpStructured) THEN
      NewLine;
      WriteLocation (instr);
      w. WriteString (" = *");
      GenDecl.WriteScalarCast (w, instr. type, FALSE, TRUE, FALSE);
      WriteAddress (instr. Greg(), instr. opndList. arg);
      w. WriteChar (";")
    ELSE
      GenDecl.VarDeclaration (w, "_src", opndType, 
        {GenDecl.doNotMark, GenDecl.ignoreMark,
         GenDecl.ignoreOtherModule, GenDecl.ignoreUsedDecl}, off);
      NewLine;
      w. WriteString ("_src = ");
      GenDecl.WriteScalarCast (w, opndType, FALSE, FALSE, FALSE);
      WriteNthArg (0, instr);
      w. WriteChar (";");
      NewLine;
      WriteLocation (instr);
      w. WriteString (" = *");      
      IF (Sym.TypeInGroup (instr. type, D.grpPointer) OR
          Sym.TypeInGroup (instr. type, D.grpProc)) THEN
        GenDecl.WriteScalarCast (w, D.struct[D.strAddress], FALSE, TRUE, FALSE)
      ELSE
        GenDecl.WriteScalarCast (w, instr. type, FALSE, TRUE, FALSE)
      END;
      w. WriteString ("&_src;")
    END;

    DEC (off);
    NewLine;
    w. WriteChar ("}")
  END TypeCastInstr;
  
PROCEDURE StructCopy (instr: D.Instruction);
  VAR
    type: D.Struct;
    
  PROCEDURE WriteScalarValue (opnd: D.Opnd);
    BEGIN
      WHILE (opnd. arg IS D.Instruction) &
            (opnd. arg(D.Instruction). opcode = Opc.typeCast) DO
        opnd := opnd. arg(D.Instruction). opndList
      END;
      WriteArg (opnd)
    END WriteScalarValue;
  
  PROCEDURE MemCopy (useSrc: BOOLEAN);
    BEGIN
      NewLine;
      w. WriteString ("(void)memcpy((void*) ");
      WriteNthArg (1, instr);
      w. WriteString (", (const void*) ");
      IF useSrc THEN
        w. WriteString ("&_src")
      ELSE
        WriteNthArg (4, instr)
      END;
      w. WriteString (", ");
      WriteNthArg (2, instr);
      w. WriteString (");")
    END MemCopy;
  
  BEGIN
    type := CastFromScalarType (instr. NthOperand (3));
    IF (type # NIL) THEN
      NewLine;
      w. WriteChar ("{");
      INC (off);
      GenDecl.VarDeclaration (w, "_src", type, 
        {GenDecl.doNotMark, GenDecl.ignoreMark,
         GenDecl.ignoreOtherModule, GenDecl.ignoreUsedDecl}, off);
      NewLine;
      w. WriteString ("_src = ");
      GenDecl.WriteScalarCast (w, type, FALSE, FALSE, FALSE);
      WriteScalarValue (instr. NthOperand (3));
      w. WriteChar (";");
      MemCopy (TRUE);
      DEC (off);
      NewLine;
      w. WriteChar ("}")
    ELSE
      MemCopy (FALSE)
    END
  END StructCopy;

PROCEDURE NewInstr (instr: D.Instruction; opc: INTEGER);
  VAR
    type, t: D.Struct;
    dim: INTEGER;
    offset: LONGINT;

  PROCEDURE AllocateBlock;
    VAR
      t: D.Struct;
      opnd: D.Opnd;
      dim: INTEGER;
      
    PROCEDURE HasPtr (t: D.Struct): BOOLEAN;
      PROCEDURE FieldPtr (obj: D.Object): BOOLEAN;
        BEGIN
          IF (obj = NIL) THEN
            RETURN FALSE
          ELSIF (obj. mode = D.objField) THEN
            RETURN HasPtr (obj. type) OR FieldPtr (obj. rightObj)
          ELSE  (* type-bound procedure *)
            RETURN FieldPtr (obj. rightObj)
          END
        END FieldPtr;

      BEGIN
        IF (t = NIL) THEN
          RETURN FALSE
        ELSE
          CASE t. form OF
          | D.strPtr, D.strPointer:
            RETURN TRUE
          | D.strArray, D.strOpenArray:
            RETURN HasPtr (t. base)
          | D.strRecord:
            RETURN HasPtr (t. base) OR FieldPtr (t. decl)
          ELSE
            RETURN FALSE
          END
        END
      END HasPtr;

    PROCEDURE WriteSize(instr: D.Instruction; type: D.Struct; offset: LONGINT);
      BEGIN
        IF (type = NIL) THEN
          WriteNthArg (0, instr)
        ELSE
          t := type;
          dim := 0;
          WHILE (t. form = D.strOpenArray) DO
            WriteNthArg (dim+1, instr);
            w. WriteChar ("*");
            t := t. base;
            INC (dim)
          END;
          w. WriteLInt (t. size, 0)
        END;
        w. WriteChar ("+");
        w. WriteLInt (offset, 0)
      END WriteSize;

    BEGIN
      IF (type # NIL) & (type. form = D.strOpenArray) THEN
        (* check that none of the (non-constant) lengths is negative *)
        t := type;
        dim := 0;
        WHILE (t. form = D.strOpenArray) DO
          opnd := instr. NthOperand (dim+1);
          IF ~(opnd. arg IS D.Const) THEN
            NewLine;
            w. WriteString ("if(");
            WriteArg (opnd);
            w. WriteString (" < 0) _invalid_length(");
            WriteArg (opnd);
            w. WriteString (", ");
            WritePos (opnd. pos);
            w. WriteString (");")
          END;
          t := t. base;
          INC (dim)
        END
      END;
      
      (* emit malloc() instruction *)
      NewLine;
      w. WriteString ("_mem = ");
      IF (gcflags. value^ # "") THEN
        IF (opc = Opc.newBlock) OR HasPtr (type) THEN
          w. WriteString ("GC_malloc")
        ELSE
          w. WriteString ("GC_malloc_atomic")
        END
      ELSE
        w. WriteString ("malloc")
      END;
      w. WriteChar ("(");
      WriteSize (instr, type, offset);
      w. WriteString (");");
      
      (* check that the malloc didn't return NIL *)
      NewLine;
      w. WriteString ("if (!_mem) _new_failed(");
      WritePos (instr. pos);
      w. WriteString (");");
      
      IF (D.instrPoisonHeap IN instr. flags) THEN
        (* initialize memory block with some byte value *)
        NewLine;
        w. WriteString ("(void)memset((void*)_mem, ");
        w. WriteLInt (StdPragmas.poisonHeap. value, 0);
        w. WriteString (", ");
        WriteSize (instr, type, offset);
        w. WriteString (");")
      ELSIF (D.instrInitialize IN instr. flags) THEN
        (* initialize memory block with zeros *)
        NewLine;
        w. WriteString ("(void)memset((void*)_mem, 0, ");
        WriteSize (instr, type, offset);
        w. WriteString (");")
      END
    END AllocateBlock;
  
  BEGIN
    IF (opc = Opc.newBlock) THEN
      type := NIL
    ELSE
      type := instr. opndList. arg(D.Struct)
    END;
    IF (type = NIL) THEN
      offset := 0
    ELSIF (type. form = D.strRecord) THEN
      IF (D.struct[D.strAddress]. size < 8) THEN  (* pad to sizeof(double) *)
        offset := 2*D.struct[D.strAddress]. size
      ELSE
        offset := D.struct[D.strAddress]. size
      END
    ELSIF (type. form = D.strArray) THEN
      offset := 0
    ELSE (* (type. form = D.strOpenArray) *)
      dim := type. OpenDimensions();
      offset := D.struct[D.strAddress]. size+dim*D.struct[D.strLongInt]. size;
      IF ((D.struct[D.strAddress]. size < 8) # ODD (dim)) THEN
        (* round to multiples of 8 *)
        INC (offset, D.struct[D.strLongInt]. size)
      END
    END;

    NewLine;
    w. WriteChar ("{");
    INC (off);
    NewLine;
    w. WriteString ("char *_mem");

    IF (type # NIL) THEN
      w. WriteString (", *_var;");
      IF (type. form = D.strOpenArray) THEN
        NewLine;
        GenDecl.WriteScalarType (w, D.struct[D.strLongInt], FALSE, FALSE);
        w. WriteString ("* _dim_ptr;")
      END;
      AllocateBlock;

      NewLine;
      w. WriteString ("_var = _mem+");
      w. WriteLInt (offset, 0);
      w. WriteChar (";");

      (* set type tag or length information *)
      IF (type. form = D.strRecord) THEN
        NewLine;
        w. WriteString ("((_Type*)_var)[-1] = &");
        GenDecl.TypeDescrName (w, type, TRUE);
        w. WriteString (".td;")
      ELSIF (type. form = D.strOpenArray) THEN
        NewLine;
        w. WriteString ("_dim_ptr = (void*)(_var-");
        w. WriteLInt (D.struct[D.strAddress]. size, 0);
        w. WriteString (");");

        t := type;
        dim := 0;
        WHILE (t. form = D.strOpenArray) DO
          NewLine;
          w. WriteString ("*(--_dim_ptr) = ");
          WriteNthArg (dim+1, instr);
          w. WriteChar (";");
          t := t. base;
          INC (dim)
        END
      END
    ELSE
      w. WriteChar (";");
      AllocateBlock
    END;

    NewLine;
    WriteLocation (instr);
    w. WriteString (" = ");
    GenDecl.WriteScalarCast (w, D.struct[D.strAddress], FALSE, FALSE, FALSE);
    IF (type = NIL) THEN
      w. WriteString ("_mem;")
    ELSE
      w. WriteString ("_var;")
    END;
    DEC (off);
    NewLine;
    w. WriteChar ("}")
  END NewInstr;


PROCEDURE AccessInstr (instr: D.Instruction; subclass: INTEGER);
  VAR
    l: A.Location;
    var: D.Object;
    greg: D.GlobalRegion;
  BEGIN  (* pre: instruction returns a non-structured value *)
    NewLine;
    WriteLocation (instr);
    w. WriteString (" = ");
    CASE subclass OF
    | Opc.subclField, Opc.subclElement, Opc.subclMem:
      IF A.PtrValue (instr. type) THEN
        GenDecl.WriteScalarCast(w, D.struct[D.strAddress], FALSE, FALSE, FALSE)
      END;
      w. WriteChar ("*");
      GenDecl.WriteScalarCast (w, instr. type, FALSE, TRUE, FALSE);
      IF (subclass = Opc.subclMem) THEN
        WriteNthArg (0, instr)
      ELSE
        WriteNthArg (1, instr)
      END
    | Opc.subclVarParam:
      var := instr. opndList. arg(D.Object);
      greg := instr. Greg();
      IF (greg. bodyOf # var. localTo) THEN
        l := A.AccessNonlocal (greg, var, "");
        w. WriteString (l. value^)
      ELSE
        IF A.PtrValue (instr. type) THEN
          GenDecl.WriteScalarCast(w, D.struct[D.strAddress], 
                                  FALSE, FALSE, FALSE)
        END;
        w. WriteChar ("*");
        WriteNthArg (0, instr)
      END
    | Opc.subclNonlocal:
      l := A.AccessNonlocal (instr. Greg(),
                             instr. opndList. arg(D.Object), "");
      w. WriteString (l. value^)
    END;
    w. WriteChar (";")
  END AccessInstr;

PROCEDURE UpdateInstr (instr: D.Instruction; subclass: INTEGER);
  VAR
    obj: D.Object;
    type: D.Struct;
    valueOpnd: D.Opnd;
    genInstr: D.Instruction;
    l: A.Location;
    greg: D.GlobalRegion;

  PROCEDURE UpdateType (instr: D.Instruction): D.Struct;
  (* Returns the type of the update's destination variable.  *)
    VAR
      opn: INTEGER;
      type: D.Struct;
      opnd: D.Opnd;
    BEGIN
      CASE instr. opcode OF
      | Opc.updateField:
        opn := 2
      | Opc.updateMem:
        opn := 1
      | Opc.updateElement:
        type := instr. opndList. OpndType();
        RETURN type. base
      | Opc.updateVarParam, Opc.updateNonlocal:
        opn := 0
      END;
      opnd := instr. NthOperand (opn);
      RETURN opnd. OpndType()
    END UpdateType;

  BEGIN
    IF (instr. opcode = Opc.updateMem) THEN
      valueOpnd := instr. NthOperand (1)
    ELSE
      valueOpnd := instr. LastOperand()
    END;
    IF (valueOpnd. arg IS D.Result) THEN
      genInstr := valueOpnd. arg(D.Result). instr
    ELSE
      genInstr := NIL
    END;
    type := UpdateType (instr);
    
    NewLine;
    CASE subclass OF
    | Opc.subclField, Opc.subclElement, Opc.subclMem:
      w. WriteString ("*");
      GenDecl.WriteScalarCast (w, type, FALSE, TRUE, FALSE);
      IF (subclass = Opc.subclMem) THEN
        WriteNthArg (0, instr)
      ELSE
        WriteNthArg (1, instr)
      END
    | Opc.subclNonlocal:
      obj := instr. opndList. arg(D.Object);
      IF (obj. localTo(D.Object). mode # D.objModule) THEN
        w. WriteChar ("*");
        WriteName (obj. localTo(D.Object));
        w. WriteString ("_")
      END;
      WriteName (obj)
    | Opc.subclVarParam:
      obj := instr. opndList. arg(D.Object);
      greg := instr. Greg();
      IF (greg. bodyOf # obj. localTo) THEN
        l := A.AccessNonlocal (greg, obj, " ");
        w. WriteString (l. value^)
      ELSE          
        w. WriteChar ("*");
        WriteNthArg (0, instr)
      END
    END;
    w. WriteString (" = ");
    IF (type. form = D.strProc) THEN
      GenDecl.WriteScalarCast (w, type, FALSE, FALSE, FALSE)
    ELSIF A.PtrValue (type) THEN
      w. WriteString ("(void*)")
    END;
    WriteArg (valueOpnd);
    w. WriteChar (";")
  END UpdateInstr;

PROCEDURE TrapInstr (instr: D.Instruction);
  BEGIN
    (* note: if type guards are disabled, then this instruction is removed
             during the final dead code elimination; there is no need to
             test if `instrIsDisabled' is set *)
    NewLine;
    CASE instr. opcode OF
    | Opc.trapReturn:
      w. WriteString ("_no_return(");
      WritePos (instr. pos)
    | Opc.trapCase:
      w. WriteString ("_case_failed(");
      WriteNthArg (0, instr);
      w. WriteString (", ");
      WritePos (instr. pos)
    | Opc.trapWith:
      w. WriteString ("_with_failed(");
      WritePos (instr. pos)
    | Opc.trapAssert:
      w. WriteString ("_assertion_failed(");
      WriteNthArg (0, instr);
      w. WriteString (", ");
      WritePos (instr. pos)
    | Opc.trapHalt:
      w. WriteString ("_halt(");
      WriteNthArg (0, instr)
    END;
    w. WriteString (");")
  END TrapInstr;

PROCEDURE ConvInstr (instr: D.Instruction);
  VAR
    from, to: D.Struct;
  BEGIN
    NewLine;
    from := instr. opndList. nextOpnd. OpndType();
    to := instr. type;
    IF Sym.TypeInGroup (from,D.grpReal) & ~Sym.TypeInGroup (to,D.grpReal) THEN
      (* converting from real to integer type by means of ENTIER; make sure 
         that rounding towards infinity is done, simple truncation won't do *)
      w. WriteString ("_entier(");
      WriteLocation (instr);
      w. WriteString (", ");
      WriteNthArg (1, instr);
      w. WriteString (")")
    ELSE
      IF Sym.TypeInGroup (from, D.grpReal) & (from. form > to. form) &
         (D.instrCheckOverflow IN instr. flags) THEN
        (* converting real value to smaller real type; if overflow checks are
           enabled check if the value fits into the target type *)
        w. WriteString ("if(!_valid_real(");
        WriteNthArg (1, instr);
        w. WriteString (")) _real_overflow(");
        WritePos (instr. pos);
        w. WriteString (");");
        NewLine
      END;
      WriteLocation (instr);
      w. WriteString (" = ");
      IF Sym.TypeInGroup (from, D.grpSet) & (to. form > from. form) THEN
        (* extending set type: clear upper bits by forcing source value into
           its original type, and converting it back to the register's type *)
        GenDecl.WriteScalarCast (w, from, FALSE, FALSE, FALSE);
        WriteNthArg (1, instr)
      ELSIF (from. form = D.strChar16) & (to. form = D.strChar8) THEN
        (* converting from LONGCHAR to CHAR: do projection *)
        GenDecl.WriteScalarCast (w, to, FALSE, FALSE, FALSE);
        WriteNthArg (1, instr)
      ELSE  (* ... implicit conversion, ignore overflow for now *)
        WriteNthArg (1, instr)
      END
    END;
    w. WriteChar (";")
  END ConvInstr;

PROCEDURE CheckZeroDiv (instr: D.Instruction; rhs: INTEGER);
  BEGIN
    IF (D.instrCheckDiv IN instr. flags) THEN
      NewLine;
      w. WriteString ("if (");
      WriteNthArg (rhs, instr);
      w. WriteString ("== 0) _");
      IF Sym.TypeInGroup (instr. type, D.grpInteger) THEN
        w. WriteString ("integer")
      ELSE
        w. WriteString ("real")
      END;
      w. WriteString ("_div_by_zero(");
      WritePos (instr. pos);
      w. WriteString (");")
    END
  END CheckZeroDiv;

PROCEDURE ArithInstr (instr: D.Instruction; class: INTEGER);
  VAR
    op: ARRAY 8 OF CHAR;
  BEGIN  (* ... overflow checks are ignored for the moment *)
    CheckZeroDiv (instr, 1);
    IF (class = Opc.classNeg) THEN
      WriteMonOp (instr, "-", 0)
    ELSIF (class = Opc.classDivInt) OR (class = Opc.classMod) THEN
      NewLine;
      IF (class = Opc.classDivInt) THEN
        w. WriteString ("_div")
      ELSE
        w. WriteString ("_mod")
      END;
      w. WriteChar ("(");
      WriteLocation (instr);
      w. WriteString (", ");
      WriteNthArg (0, instr);
      w. WriteString (", ");
      WriteNthArg (1, instr);
      w. WriteString (", ");
      GenDecl.WriteScalarType (w, instr. type, FALSE, FALSE);
      w. WriteString (");")
    ELSE
      CASE class OF
      | Opc.classAdd    : op := "+"
      | Opc.classSub    : op := "-"
      | Opc.classMult   : op := "*"
      | Opc.classDivReal: op := "/"
      END;
      WriteDyOp (instr, op, 0, 1)
    END
  END ArithInstr;

PROCEDURE PredefFunction (instr: D.Instruction; class: INTEGER);
  PROCEDURE ShiftName (arg: D.Usable; name, posSuffix, negSuffix: ARRAY OF CHAR);
    BEGIN
      NewLine;
      WriteLocation (instr);
      w. WriteString (" = ");
      GenDecl.WriteScalarCast (w, instr. type, FALSE, FALSE, FALSE);
      w. WriteString (name);
      WITH arg: D.Const DO
        IF (arg. int > 0) THEN
          w. WriteString (posSuffix)
        ELSE
          w. WriteString (negSuffix)
        END
      ELSE
      END;
      w. WriteChar ("(")
    END ShiftName;

  PROCEDURE ShiftCountRot (shift: D.Opnd; bits: LONGINT);
    BEGIN
      IF (shift. arg IS D.Const) THEN
        w. WriteLInt (shift. arg(D.Const). int MOD bits, 0)
      ELSE
        WriteArg (shift)
      END;
      w. WriteString (", ");
      w. WriteLInt (bits, 0)
    END ShiftCountRot;

  PROCEDURE ShiftCount (shift: D.Opnd);
    BEGIN
      IF (shift. arg IS D.Const) THEN
        w. WriteLInt (ABS (shift. arg(D.Const). int), 0)
      ELSE
        WriteArg (shift)
      END
    END ShiftCount;

  BEGIN  (* ... overflow checks are ignored for the moment *)
    CASE class OF
    | Opc.classAbs:
      WriteMonCall (instr, "_abs", 0)
    | Opc.classAsh:
      ShiftName (instr. NthArgument (1), "_ash", "l", "r");
      WriteNthArg (0, instr);
      w. WriteString (", ");
      ShiftCount (instr. NthOperand (1));
      w. WriteString (", ");
      GenDecl.WriteScalarCast (w, instr. type, TRUE, FALSE, FALSE);
      w. WriteString (");")
    | Opc.classCap:
      IF (instr. type. form = D.strChar8) THEN
        WriteMonCall (instr, "_cap", 0)
      ELSE
        WriteMonCall (instr, "_capl", 0)
      END
    | Opc.classOdd:
      WriteMonCall (instr, "_odd", 0)
    | Opc.classLsh:
      ShiftName (instr. NthArgument (1), "_lsh", "l", "r");
      WriteNthArg (0, instr);
      w. WriteString (", ");
      ShiftCount (instr. NthOperand (1));
      w. WriteString (", ");
      GenDecl.WriteScalarCast (w, instr. type, TRUE, FALSE, FALSE);
      w. WriteString (");")
    | Opc.classRot:
      ShiftName (instr. NthArgument (1), "_rot", "_const", "_const");
      WriteNthArg (0, instr);
      w. WriteString (", ");
      ShiftCountRot (instr. NthOperand (1), instr. type. size*8);
      w. WriteString (", ");
      GenDecl.WriteScalarCast (w, instr. type, TRUE, FALSE, FALSE);
      w. WriteString (");")
    END
  END PredefFunction;

PROCEDURE SetInstr (instr: D.Instruction; class: INTEGER);
  VAR
    op: ARRAY 4 OF CHAR;
  BEGIN
    IF (class = Opc.classCompl) THEN
      WriteMonOp (instr, "~", 0)

    ELSIF (class = Opc.classBitClear) OR (class = Opc.classBitSet) OR
          (class = Opc.classDiff) THEN
      NewLine;
      WriteLocation (instr);
      w. WriteString (" = ");
      WriteNthArg (0, instr);
      IF (class = Opc.classBitSet) THEN
        w. WriteString (" | (")
      ELSE
        w. WriteString (" & ~(")
      END;
      WriteResultCast (instr, TRUE);
      IF (class # Opc.classDiff) THEN
        w. WriteString ("1 << ")
      END;
      WriteNthArg (1, instr);
      w. WriteString (");")

    ELSIF (class = Opc.classBitTest) THEN
      NewLine;
      WriteLocation (instr);
      w. WriteString (" = (");
      WriteNthArg (0, instr);
      w. WriteString (" & (");
      WriteResultCast (instr, TRUE);
      w. WriteString ("1 << ");
      WriteNthArg (1, instr);
      w. WriteString (")) != 0;")
    
    ELSIF (class = Opc.classBitRange) THEN
      NewLine;
      WriteLocation (instr);
      w. WriteString (" = _bit_range(");
      WriteResultCast (instr, TRUE);
      w. WriteString (", ");
      WriteNthArg (0, instr);
      w. WriteString (", ");
      WriteNthArg (1, instr);
      w. WriteString (");")

    ELSE
      CASE class OF
      | Opc.classInter: op := "&"
      | Opc.classSymDiff: op := "^"
      | Opc.classUnion: op := "|"
      END;
      WriteDyOp (instr, op, 0, 1)
    END
  END SetInstr;

PROCEDURE CompareInstr (instr: D.Instruction; class, subclass: INTEGER);
  VAR
    str: ARRAY 64 OF CHAR;
    
  PROCEDURE WriteRelation (class: INTEGER);
    VAR
      op: ARRAY 3 OF CHAR;
    BEGIN
      CASE class OF
      | Opc.classEql: op := "=="
      | Opc.classNeq: op := "!="
      | Opc.classLss: op := "<"
      | Opc.classLeq: op := "<="
      | Opc.classGtr: op := ">"
      | Opc.classGeq: op := ">="
      END;
      w. WriteString (op)
    END WriteRelation;

  BEGIN
    NewLine;
    WriteLocation (instr);
    w. WriteString (" = ");
    IF (subclass >= Opc.subclStr) THEN  (* string comparison *)
      IF (subclass = Opc.subclStr) THEN
        w. WriteString ("strcmp((const char*) ");
        WriteNthArg (2, instr);
        w. WriteString (", (const char*) ")
      ELSE
        StdTypes.BasicTypes (D.strChar16, str);
        w. WriteString ("strcmpl((const ");
        w. WriteString (str);
        w. WriteString ("*) ");
        WriteNthArg (2, instr);
        w. WriteString (", (const ");
        w. WriteString (str);
        w. WriteString ("*) ")
      END;
      WriteNthArg (3, instr);
      w. WriteString (") ");
      WriteRelation (class);
      w. WriteString (" 0")
    ELSE
      WriteNthArg (0, instr);
      w. WriteChar (" ");
      WriteRelation (class);
      w. WriteChar (" ");
      WriteNthArg (1, instr)
    END;
    w. WriteString (";")
  END CompareInstr;



PROCEDURE AssignToGates (merge: D.Merge; r: D.Region);
(* For all gates in `merge' assign the gate argument corresponding to region
   `r' to the gate variable.  If necessary introduce temporary variables to
   deal with swaps between variables.  *)
  VAR
    opn, i, schedEnd: INTEGER;
    use, opnd: D.Opnd;
    counter, auxCounter: INTEGER;
    loc: A.Location;
    
  PROCEDURE AddAssignment (src: D.Opnd; srcLoc, destLoc: A.Location; cat: SHORTINT);
    VAR
      i: LONGINT;
      new: AssignArray;
    BEGIN
      IF (counter = LEN (assignArray^)) THEN
        NEW (new, counter+16);
        FOR i := 0 TO counter-1 DO
          new[i] := assignArray[i]
        END;
        assignArray := new
      END;
      assignArray[counter]. src := src;
      assignArray[counter]. srcLoc := srcLoc;
      assignArray[counter]. destLoc := destLoc;
      assignArray[counter]. cat := cat;
      INC (counter)
    END AddAssignment;
  
  PROCEDURE Arrange (schedEnd: INTEGER): INTEGER;
  (* Arrange the assignments starting at index `schedEnd' in such a way that
     the left hand side of an assigment has no further use as a right hand side
     in one of the following assignments.  Return the index of the first 
     assignment that couldn't be moved around to honor that rule, or the index
     after the last assignment.  *)
    VAR
      h: Assignment;
      i, prevEnd: INTEGER;
    
    PROCEDURE Schedulable (i: INTEGER): BOOLEAN;
      VAR
        j: INTEGER;
      BEGIN
        FOR j := schedEnd TO counter-1 DO
          IF (j # i) &
             (assignArray[j]. srcLoc # NIL) &
             (assignArray[j]. srcLoc. value^ = 
              assignArray[i]. destLoc. value^) THEN
            RETURN FALSE
          END
        END;
        RETURN TRUE
      END Schedulable;
    
    BEGIN
      REPEAT
        prevEnd := schedEnd;
        i := schedEnd;
        WHILE (i < counter) DO
          IF Schedulable (i) THEN
            h := assignArray[i]; 
            assignArray[i] := assignArray[schedEnd]; 
            assignArray[schedEnd] := h;
            INC (schedEnd)
          END;
          INC (i)
        END
      UNTIL (prevEnd = schedEnd);
      RETURN schedEnd
    END Arrange;
  
  PROCEDURE IntroduceAuxVar (i: INTEGER);
  (* Create a new auxiliary variable and assign the value of the destination of
     the assignment `i' to it.  Replace all further uses of the location of
     `i' with the auxiliary variable.  *)
    VAR
      j: INTEGER;
      str: ARRAY 64 OF CHAR;
    BEGIN
      IF (auxCounter = 0) THEN  (* create new block *)
        NewLine;
        w. WriteChar ("{");
        INC (off)
      END;
      NewLine;
      A.WriteRegType (w, assignArray[i]. cat);
      IntStr.IntToStr (auxCounter, str);
      Strings.Insert (Class.prefixAuxiliary, 0, str);
      w. WriteString (str);
      
      w. WriteString (" = ");
      w. WriteString (assignArray[i]. destLoc. value^);
      w. WriteChar (";");
      INC (auxCounter);
      
      loc := A.NewLoc (str);
      FOR j := i TO counter-1 DO
        IF (assignArray[j]. srcLoc # NIL) &
           (assignArray[j]. srcLoc. value^ = assignArray[i]. destLoc. value^) THEN
          assignArray[j]. srcLoc := loc
        END
      END
    END IntroduceAuxVar;
  
  BEGIN
    counter := 0;
    opn := merge. ArgumentIndex (r)+1;
    use := merge. useList;
    WHILE (use # NIL) DO
      IF (use. instr. opcode = Opc.gate) &
         ~(Class.instrVoid IN use. instr. flags) THEN
        opnd := use. instr. NthOperand (opn);
        IF ~(opnd. arg IS D.Object) THEN
          IF (opnd. arg IS D.Result) THEN
            loc := opnd. arg(D.Result). location(A.Location)
          ELSE
            loc := NIL
          END;
          AddAssignment (opnd, loc, use. instr. location(A.Location),
                         Class.RegClass (use. instr. type))
        (* ELSE: gate operand is undefined value or a structure *)
        END
      END;
      use := use. nextUse
    END;
    
    (* arrange assignments and introduce auxiliary variables *)
    auxCounter := 0;
    schedEnd := 0;
    WHILE (schedEnd # counter) DO
      schedEnd := Arrange (schedEnd);
      IF (schedEnd # counter) THEN
        IntroduceAuxVar (schedEnd)
      END
    END;
    
    (* emit assignments *)
    FOR i := 0 TO counter-1 DO
      IF (assignArray[i]. srcLoc = NIL) OR
         (assignArray[i]. destLoc. value^ # assignArray[i]. srcLoc. value^) THEN
        (* avoid assignments of the form `x = x' *) 
        NewLine;
        w. WriteString (assignArray[i]. destLoc. value^);
        w. WriteString (" = ");
        IF (assignArray[i]. srcLoc # NIL) THEN
          w. WriteString (assignArray[i]. srcLoc. value^);
        ELSE
          WriteArg (assignArray[i]. src)
        END;
        w. WriteChar (";")
      END
    END;
    IF (auxCounter # 0) THEN
      DEC (off);
      NewLine;
      w. WriteChar ("}")
    END
  END AssignToGates;


PROCEDURE Label (instr: D.Instruction);
  VAR
    old: INTEGER;
  BEGIN
    old := off; off := 0;
    NewLine;
    w. WriteChar ("l");
    w. WriteLInt (instr. marker, 0);
    w. WriteChar (":");
    off := old
  END Label;

PROCEDURE Goto (instr: D.Instruction; newline: BOOLEAN);
  BEGIN
    IF (instr # NIL) THEN
      IF newline THEN
        NewLine
      END;
      w. WriteString ("goto l");
      w. WriteLInt (instr. marker, 0);
      w. WriteChar (";")
    END
  END Goto;

PROCEDURE Region (r: D.Region);
(* Writes the instructions of region `r' in sequence.  If `r' is merged into
   a merge region `m', and `m' should be emitted as part of `r', then do
   this.  *)
  VAR
    instr: D.Instruction;
    opnd: D.Opnd;
    opc, class, subclass: INTEGER;
    str: ARRAY 128 OF CHAR;
    negate: BOOLEAN;

  PROCEDURE MarkForwardReference (instr: D.Instruction);
  (* Checks all references to functions and marks all procedures not emitted
     yet with `objNeedPrototype'.  This will place the necessary function
     prototypes at the end of the .d file.  *)
    VAR
      obj: D.Object;
    BEGIN
      obj := instr. opndList. arg(D.Object);
      IF (obj. mode IN {D.objProc, D.objTBProc}) &
         (obj. beFlags * {StdTypes.objEmitted, StdTypes.objInProgress} = {}) THEN
        INCL (obj. beFlags, StdTypes.objNeedPrototype)
      END
    END MarkForwardReference;

  PROCEDURE CaseGuard (select: D.Opnd; labelList: D.Opnd);
  (* Write a case guard as a sequence of compare expressions.  *)
    VAR
      label: D.Opnd;
      range, const: D.Const;
      type: D.Struct;
      min, max: LONGINT;

    PROCEDURE Compare (op: ARRAY OF CHAR; int: LONGINT);
      BEGIN
        WriteArg (select);
        w. WriteString (op);
        GenConst.Int (w, int)
      END Compare;

    BEGIN
      type := select. OpndType();
      const := StdTypes.Min (type. form);
      min := const. int;
      const := StdTypes.Max (type. form);
      max := const. int;

      (* write boolean expression with a lot of compare instructions; avoid
         silly compares like -128<=i, where i is a SHORTINT; note that the 
         actual range of the labels may be larger than that of the type of the
         selector operation, if selector is the result of a type conversion 
         that the ANSI-C backend decided to skip; therefore the test uses 
         "<= min" instead of "= min" (and for max) *)
      label := labelList;
      WHILE (label # NIL) DO
        IF (label # labelList) THEN
          w. WriteString (" || ")
        END;
        range := label. arg(D.Const);
        IF (range. int = range. int2) THEN
          Compare ("==", range. int)
        ELSIF (range. int <= min) THEN
          Compare ("<=", range. int2)
        ELSIF (range. int2 >= max) THEN
          Compare (">=", range. int)
        ELSE
          w. WriteChar ("(");
          Compare (">=", range. int);
          w. WriteString (" && ");
          Compare ("<=", range. int2);
          w. WriteChar (")")
        END;
        label := label. nextOpnd
      END
    END CaseGuard;

  BEGIN
    instr := r. instrList;
    WHILE (instr # NIL) DO
      IF (Class.instrJumpTarget IN instr. flags) THEN
        (* `instr' will translate to C code, i.e. `instrNoOuput' is not set or
           it is an access/update-heap with `instrCheckNil' enabled *)
        Label (instr)
      END;

      currId := instr. marker;
      IF (instr IS D.Region) THEN
        IF writeSyncStatm. true & WriteGSA.writeGSA. true THEN
          Out.String ("region (");
          Out.LongInt (instr. marker, 0);
          Out.String (") ");
          WriteGSA.Opcode (instr. opcode, str);
          Out.Ln
        END;

        Region (instr(D.Region))
      ELSE
        IF writeSyncStatm. true & WriteGSA.writeGSA. true THEN
          Out.Char ("(");
          Out.LongInt (instr. marker, 0);
          Out.String (") ");
          WriteGSA.Opcode (instr. opcode, str);
          Out.String (str);
          Out.Ln
        END;

        opc := instr. opcode;

        IF (opc = Opc.accessHeap) OR (opc = Opc.updateHeap) THEN
          (* insert test against NIL for access/update of heap, regardless if
             the instruction was classified as having no output or not *)
          CheckNil (instr, 1)
        ELSE
          (* collect operand values to memory for selected instructions;
             note that procedure calls are handled separately *)
          CASE opc OF
          | Opc.updateMem, Opc.accessMem, Opc.bit, Opc.move:
            CollectToMem (r. Greg(), instr)
          ELSE
          END
        END;

        IF (opc = Opc.adr) & (instr. opndList. arg IS D.Object) THEN
          MarkForwardReference (instr)

        ELSIF ~(Class.instrNoOutput IN instr. flags) THEN
          class := opc DIV Opc.sizeClass;
          subclass := opc MOD Opc.sizeClass;

          CASE class OF
          | 0..Opc.classAccess-1:
            CASE opc OF
            | Opc.enter:
              (* ... *)
            | Opc.exit:
              ExitInstr (instr)
            | Opc.call:
              CallInstr (instr)
            | Opc.arrayLength:
              ArrayLength (instr)
            | Opc.typeTag:
              CheckNil (instr, 0);
              NewLine;
              WriteLocation (instr);
              w. WriteString (" = *");
              GenDecl.WriteScalarCast (w, D.struct[D.strAddress], FALSE,
                                       TRUE, FALSE);
              w. WriteChar ("(");
              WriteNthArg (0, instr);
              w. WriteChar ("-");
              w. WriteLInt (D.struct[D.strAddress]. size, 0);
              w. WriteString (");")
            | Opc.tbProcAdr:
              TBProcAddress (instr)
            | Opc.boundIndex, Opc.boundRange:
              BoundInstr (instr)
            | Opc.typeTest:
              TypeTest (instr)
            | Opc.typeGuard:
              TypeGuard (instr)
            | Opc.typeAssert:
              TypeAssertion (instr)
            | Opc.zero:
              NewLine;
              w. WriteString ("(void)memset((void*) ");
              WriteNthArg (1, instr);
              w. WriteString (", 0, ");
              w. WriteLInt (instr. type. size, 0);
              w. WriteString (");")
            | Opc.copy:
              WriteMonOp (instr, "", 0)
            | Opc.bit:
              WriteDyCall (instr, "_bit", 0, 1)
            | Opc.typeCast:
              TypeCastInstr (instr)
            | Opc.stringCopy:
              NewLine;
              w. WriteString ("_string_copy");
              IF Sym.TypeInGroup (instr. opndList. OpndType(), D.grpString16) THEN
                opnd := instr. NthOperand (3);
                IF Sym.TypeInGroup (opnd. OpndType(), D.grpString8) THEN
                  w. WriteString ("2")
                END;
                w. WriteString ("l")
              END;
              w. WriteString ("(");
              WriteNthArg (1, instr);
              w. WriteString (", ");
              WriteNthArg (4, instr);
              w. WriteString (", ");
              WriteNthArg (2, instr);
              w. WriteString (");")
            | Opc.structCopy:
              StructCopy (instr)
            | Opc.new, Opc.newBlock:
              NewInstr (instr, opc)
            | Opc.move:
              NewLine;
              w. WriteString ("(void)memcpy((void*) ");
              WriteNthArg (1, instr);
              w. WriteString (", (const void*) ");
              WriteNthArg (0, instr);
              w. WriteString (", ");
              WriteNthArg (2, instr);
              w. WriteString (");")
            ELSE
              (* ignored instruction; note: gates are handled as part of the 
                 merged regions *)
            END
          | Opc.classAccess:
            AccessInstr (instr, subclass)
          | Opc.classUpdate:
            UpdateInstr (instr, subclass)
          | Opc.classTrap:
            TrapInstr (instr)
          | Opc.classAdd..Opc.classNeg:
            ArithInstr (instr, class)
          | Opc.classAbs..Opc.classRot:
            PredefFunction (instr, class)
          | Opc.classInter..Opc.classBitTest:
            SetInstr (instr, class)
          | Opc.classNot:
            WriteMonOp (instr, "!", 0)
          | Opc.classEql..Opc.classGeq:
            CompareInstr (instr, class, subclass)
          | Opc.classConv:
            IF (instr. useList # NIL) THEN (* hasn't been replaced by opnd *)
              ConvInstr (instr)
            END
          ELSE
            CASE opc OF
            | ControlFlow.jump:
              Goto (instr. opndList. arg(D.Instruction), TRUE)
            | ControlFlow.branchOnTrue, ControlFlow.branchOnFalse:
              NewLine;
              w. WriteString ("if (");
              negate := (opc = ControlFlow.branchOnFalse) &
                        ((r. opcode = Opc.guardCase) OR 
                          (r. opcode = Opc.guardTrue)) OR
                        (opc = ControlFlow.branchOnTrue) &
                          (r. opcode = Opc.guardFalse);
              IF negate THEN
                w. WriteString ("!(")
              END;
              IF (r. opcode = Opc.guardCase) THEN
                CaseGuard (r. opndList, r. opndList. nextOpnd)
              ELSE
                WriteNthArg (0, r)
              END;
              IF negate THEN
                w. WriteChar (")")
              END;
              w. WriteString (") ");
              Goto (instr. opndList. arg(D.Instruction), FALSE)
            | ControlFlow.assignGates:
              AssignToGates (instr. opndList. arg(D.Merge), r)
            | ControlFlow.endOfGreg:
              (* no operation, only present to serve as target of jump; ANSI-C
                 forbids labels at the end of a compound statement, but putting
                 one in front of the empty statement is legal *)
              IF (Class.instrJumpTarget IN instr. flags) THEN
                NewLine;
                w. WriteChar (";")
              END
            END
          END
        END
      END;
      instr := instr. nextInstr
    END
  END Region;

PROCEDURE GlobalRegion* (greg: D.GlobalRegion);
(* Emits code for global region `greg', i.e. the body of a C function.  *)
  VAR
    i: LONGINT;
    enter: D.Instruction;

  PROCEDURE CopyValueParams (fpars: D.Struct): BOOLEAN;
  (* Creates storage to hold local values of value parameters and copy the
     parameters into it.  Has to be called after the local declarations of the
     procedure have been written, put before any statement has been emitted. *)
    VAR
      fpar: D.Object;
      localOpenArray: BOOLEAN;
      i: INTEGER;
      t: D.Struct;
    BEGIN
      (* dependence analysis should provide information to avoid unnecessary 
         copies of value parameters; the static check is done in procedure 
         CodeGen.EmitProcedure before the function header in written; the
         run-time check is not implemented yet ... *)

      (* 1st pass over formal pars: allocate local variables for value
         parameters of structured types, but not for open arrays *)
      localOpenArray := FALSE;
      fpar := fpars. decl;
      WHILE (fpar # NIL) DO
        IF (StdTypes.objLocalCopy IN fpar. beFlags) THEN
          IF (fpar. type. form = D.strOpenArray) THEN
            localOpenArray := TRUE
          END;
          GenDecl.Declaration (w, fpar, {GenDecl.doNotMark,
                               GenDecl.ignoreMark, GenDecl.ignoreUsedDecl}, 1)
        END;
        fpar := fpar. rightObj
      END;
      IF localOpenArray & (valueStack. value >= 0) THEN
        NewLine;
        w. WriteString ("char* _old_top_vs = _top_vs;");
      END;

      (* 2nd pass over formal vars: allocate memory for open arrays, and create
         copy instructions to move value parameter into its local variable  *)
      fpar := fpars. decl;
      WHILE (fpar # NIL) DO
        IF (StdTypes.objLocalCopy IN fpar. beFlags) THEN
          IF (fpar. type. form # D.strOpenArray) THEN
            NewLine;
            w. WriteString ("(void)memcpy(&");
            WriteName (fpar);
            w. WriteString (", ");
            WriteName (fpar);
            w. WriteString ("__ref, ");
            w. WriteLInt (fpar. type. size, 0);
            w. WriteString (");")
          ELSE
            NewLine;
            IF (valueStack. value < 0) THEN
              w. WriteString ("_push_value_alloca(")
            ELSIF (D.instrStackCheck IN enter. flags) THEN
              w. WriteString ("_push_value_ov(")
            ELSE
              w. WriteString ("_push_value(")
            END;
            GenDecl.WriteScalarType (w, D.struct[D.strAddress], FALSE, FALSE);
            w. WriteString (", ");
            WriteName (fpar);
            w. WriteString (", ");
            WriteName (fpar);
            w. WriteString ("__ref, ");

            (* write size of actual parameter *)
            i := 0;
            t := fpar. type;
            WHILE (t. form = D.strOpenArray) DO
              WriteName (fpar);
              w. WriteChar ("_");
              w. WriteLInt (i, 0);
              w. WriteString ("d");
              t := t. base;
              IF (t. size # 1) THEN
                w. WriteChar ("*")
              END;
              INC (i)
            END;
            IF (t = fpar. type) OR (t. size # 1) THEN
              w. WriteLInt (t. size, 0)
            END;

            IF (valueStack. value >= 0) & 
               (D.instrStackCheck IN enter. flags) THEN
              w. WriteString (", ");
              WritePos (greg. bodyOf. pos)
            END;
            w. WriteString (");")
          END
        END;
        fpar := fpar. rightObj
      END;

      RETURN localOpenArray
    END CopyValueParams;

  BEGIN
    (* global region: emit a function prologue that creates copies of value
       parameters, followed by the instructions; note that while the enter
       instruction is always part of the global region, the exit instruction
       (and the procedure epilogue) may be nested into another region or can
       be absent *)
    enter := greg. EnterInstr();
    off := 1;
    IF (greg. bodyOf. mode # D.objModule) THEN
      localOpenArray := CopyValueParams (greg. bodyOf. type)
    ELSE
      localOpenArray := FALSE
    END;
    IF (greg. bodyOf. mode = D.objTBProc) THEN
      INCL (greg. bodyOf. beFlags, StdTypes.objNeedPrototype)
    END;
    Region (greg);

    (* cleanup array of assignments *)
    FOR i := 0 TO LEN (assignArray^)-1 DO
      assignArray[i]. src := NIL;
      assignArray[i]. destLoc := NIL;
      assignArray[i]. srcLoc := NIL
    END
  END GlobalRegion;

PROCEDURE EmitLocalVars* (obj: D.Object);
(* Emits all variable declarations in the subtree `obj' that are used further 
   down. *)
  
  PROCEDURE UndefinedUse (obj: D.Object): BOOLEAN;
    VAR
      use: D.Opnd;
    BEGIN
      use := obj. useList;
      WHILE (use # NIL) DO
        IF use. ValueOperand() THEN
          (* somewhere the variable object is used as argument in a position
             that expects a value; in other words: there exists an access to 
             an undefined value of the variable `obj' *)
          RETURN TRUE
        END;
        use := use. nextUse
      END;
      RETURN FALSE
    END UndefinedUse;
  
  BEGIN
    IF (obj # NIL) THEN
      EmitLocalVars (obj. leftObj);
      IF (obj. mode = D.objVar) & ~(D.objIsParameter IN obj. flags) &
         ((StdTypes.objUsedLocalVar IN obj. beFlags) OR UndefinedUse (obj)) THEN
        GenDecl.Declaration (w, obj,
           {GenDecl.ignoreUsedDecl, GenDecl.doNotMark}, 1)
      END;
      EmitLocalVars (obj. rightObj)
    END
  END EmitLocalVars;

BEGIN
  NEW (assignArray, 32);
  currId := -1;
  opList := "*/%+-&^|";
  
  writeSyncStatm := ParamOptions.CreateBoolean ("writeSyncStatm", FALSE);
  ParamOptions.options. CmdLineOption ("--cgsa-sync-statm", "writeSyncStatm:=TRUE");
  ParamOptions.options. Add (writeSyncStatm);

  valueStack := ParamOptions.CreateInteger ("valueStack", Config.defaultValueStack, -1, MAX(LONGINT));
  ParamOptions.options. Add (valueStack);

  gcflags := ParamOptions.CreateString ("gcflags", Config.defaultGcFlags);
  ParamOptions.options. Add (gcflags);
  ParamOptions.options. CmdLineOption ("--gcflags", "gcflags:='$1'")
END GenStatm.
