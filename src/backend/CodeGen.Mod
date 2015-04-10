(* 	$Id: CodeGen.Mod,v 1.51 2001/04/07 12:16:25 ooc-devel Exp $	 *)
MODULE CodeGen;
(*  Code generation part of oo2c.
    Copyright (C) 1995-1999, 2001  Michael van Acken

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
  Strings, Out, ParamOptions, Files, TextRider, FileData, SystemFlags, Make,
  E := Error, D := Data, Opc := Opcode, Sym := SymbolTable, WriteGSAvC,
  SymbolFile, StdTypes, SideEffects, GenDecl, GenInclude, GenConst, GenStatm, 
  External, Classify, Schedule, Allocate, ControlFlow, Build, GuardCond, Check,
  GuardPropagation, GateReduction, AlgebraicTransformation, ConstPropagation,
  DeadCodeElimination, ValueNumbering, CopyPropagation, AliasAnalysis,
  LoopTransformation, WriteGSA;


VAR
  translationBasis-: ParamOptions.StringOption;

CONST  (* valid values for `translationBasis. value' *)
  translateGlobProc* = "gproc";  (* one global procedure (incl nested procs) at a time *)
  translateModule* = "module";
  translateProgram* = "program";
  translationDefault = translateGlobProc;  (* default for `translationBasis' *)

CONST
  useDefaultOpt* = "???";
  
TYPE
  Program* = POINTER TO ProgramDesc;
  Module* = POINTER TO ModuleDesc;
  Procedure* = POINTER TO ProcedureDesc;
  
  ProgramDesc = RECORD
    moduleList-: Module;         (* list of imported modules *)
    buildLib-: External.Lib;     (* set if we are building a library *)
  END;
  ModuleDesc = RECORD
    nextModule-: Module;
    progData: Program;           (* pointer to program desc; can be NIL *)
    obj-: D.Object;              (* the module's symbol table *)
    symbolFileMagic-: LONGINT;   (* fingerprint of generated symbol file *)
    procList: Procedure;         (* list of procedures *)
    body: D.GlobalRegion;        (* module body *)
    structList: Sym.StructList;  (* list of ARRAY and RECORD constructors *)
  END;
  ProcedureDesc = RECORD
    nextProc: Procedure;
    obj: D.Object;               (* the procedure's local declarations *)
    body: D.GlobalRegion         (* procedure body *)
  END;


(* this data structure is used to implement the --opt option *)
TYPE
  TransformProc = PROCEDURE (r: D.Region);
  CodeTransform = POINTER TO CodeTransformDesc;
  CodeTransformDesc = RECORD
    next: CodeTransform;
    name: ARRAY 48 OF CHAR;  (* name of optimization *)
    id: CHAR;                (* opt id, used for the --opt option *)
    flags: SET;
    proc: TransformProc      (* procedure that implements the opt *)
  END;

CONST  (* valid values for `CodeTransformDesc.flags' *)
  ctNeedsGuardCond = 0;  
  (* transformation needs `GuardCond.Init' to be run beforehand *)
  ctKeepsGuardCond = 1;
  (* transformation doesn't touch information created by `GuardCond.Init' *)

VAR
  ctProcs: CodeTransform;
  optimizers-: ParamOptions.StringOption;     (* string of optimizer ids *)
  stupidCodeGen-: ParamOptions.BooleanOption; (* disables all optmizations *)
  checks: ParamOptions.BooleanOption;         (* run checks before/after opt *)

VAR
  hFile, dFile, cFile: FileData.FileData;
  hWriter, dWriter, cWriter: TextRider.Writer;
  

PROCEDURE FindProc (id: CHAR): CodeTransform;
  VAR
    ct: CodeTransform;
  BEGIN
    ct := ctProcs;
    WHILE (ct # NIL) & (ct. id # id) DO
      ct := ct. next
    END;
    RETURN ct
  END FindProc;

PROCEDURE CheckOptimizers*;
  VAR
    i: INTEGER;
    ct: CodeTransform;
  BEGIN
    FOR i := 0 TO Strings.Length (optimizers. value^)-1 DO
      ct := FindProc (optimizers. value[i]);
      IF (ct = NIL) THEN
        Out.String ("Illegal optimization id `"); 
        Out.Char (optimizers. value[i]);
        Out.String ("'.  Valid values:"); Out.Ln;
        ct := ctProcs;
        WHILE (ct # NIL) DO
          Out.String ("  "); Out.Char (ct. id);
          Out.String (" "); Out.String (ct. name); Out.Ln;
          ct := ct. next
        END;
        HALT (1)
      END
    END
  END CheckOptimizers;

PROCEDURE WriteGSACode (r: D.Region);
  BEGIN
    (* mh, should change TransformProc to accept a GlobalRegion as parameter
       ... someday *)
    WriteGSA.Body (r(D.GlobalRegion))
  END WriteGSACode;


PROCEDURE InstallOptimizers;
  PROCEDURE AddProc (name: ARRAY OF CHAR; id: CHAR; proc: TransformProc; 
                     flags: SET);
    VAR
      ct: CodeTransform;
    BEGIN
      NEW (ct);
      ct. next := ctProcs;
      COPY (name, ct. name);
      ct. id := id;
      ct. proc := proc;
      ct. flags := flags;
      ctProcs := ct
    END AddProc;
  
  BEGIN
    ctProcs := NIL;
    AddProc ("write GSA code", "?", WriteGSACode, {});
    AddProc ("suppress final dead code elimination", "0", NIL, {});
    AddProc ("dead code elimination and remove disabled instr", "1", NIL, {});
    AddProc ("dead code elimination", "D", NIL, {});
    AddProc ("alias analysis", "a", AliasAnalysis.Analyse, {});
    AddProc ("loop transformation", "l", LoopTransformation.GlobalRegion, {});
    AddProc ("guard propagation", "g", GuardPropagation.Propagate, 
             {ctNeedsGuardCond, ctKeepsGuardCond});
    AddProc ("gate reduction", "G", GateReduction.Reduce, 
             {ctNeedsGuardCond, ctKeepsGuardCond});
    AddProc ("common subexpression elimination", "C", ValueNumbering.Number, {});
    AddProc ("algebraic transformation", "A", 
             AlgebraicTransformation.Transform, {});
    AddProc ("constant propagation", "c", ConstPropagation.ConstPropagation, 
             {})
  END InstallOptimizers;



PROCEDURE OptimizeBlock (greg: D.GlobalRegion);
  VAR
    i: INTEGER;
    ct: CodeTransform;
    guardCondValid: BOOLEAN;
    
  PROCEDURE NoDCE (opt: ARRAY OF CHAR): BOOLEAN;
    VAR
      i: INTEGER;
    BEGIN
      i := 0;
      WHILE (opt[i] # 0X) & (opt[i] # "0") DO
        INC (i)
      END;
      RETURN (opt[i] = "0")
    END NoDCE;
  
  BEGIN
    IF (greg # NIL) THEN
      (* copy propagation and dead code elimination are already done
         by the front-end (unless ParseDecl.removeDeadCode isn't set);
         `ParseDecl.Module' returns with valid `GuardCond' information *)
      IF checks. true & ~Check.All (greg) THEN
        Out.String ("Code emitted by front-end didn't pass consistency checks, aborting");
        Out.Ln;
        HALT (1)
      END;

      IF stupidCodeGen. true THEN
        CopyPropagation.Propagate (greg); (* get rid of copies *)
        greg. ClearInfo (0);  (* clear all info entries to free memory *)
        RETURN
      END;
        
      guardCondValid := TRUE;
      i := 0; 
      WHILE (optimizers. value[i] # 0X) DO
        ct := FindProc (optimizers. value[i]);
        IF (ct. proc # NIL) THEN
          IF (ctNeedsGuardCond IN ct. flags) & ~guardCondValid THEN
            GuardCond.Init (greg);
            guardCondValid := TRUE
          END; 
          ct. proc (greg);
          
          IF checks. true & ~Check.All (greg) THEN
            Out.String ("Error: ");
            Out.String (ct. name);
            Out.String (" violated GSA invariant, aborting");
            Out.Ln;
            HALT (1)
          END;
          
          IF ~(ctKeepsGuardCond IN ct. flags) THEN
            IF guardCondValid THEN
              greg. ClearInfo (0)      (* clear to free memory *)
            END;
            guardCondValid := FALSE
          END
        ELSIF (ct. id = "D") OR (ct. id = "1") THEN (* dead code elimination *)
          DeadCodeElimination.Eliminate (greg, ct. id = "1");
          IF guardCondValid THEN
            GuardCond.RemoveDeadReferences (greg)
          END
        END;
        INC (i)
      END;
      
      IF ~NoDCE (optimizers. value^) THEN
        (* final dead code elimination to get rid of disabled instructions *)
        DeadCodeElimination.Eliminate (greg, TRUE)
      END;
      
      greg. ClearInfo (0)  (* clear all info entries to free memory *)
    END
  END OptimizeBlock;

PROCEDURE OptimizeModule (modData: Module);
  VAR
    proc: Procedure;
  BEGIN
    (* module based optimizations can be placed here, or after the greg
       based ones ... *)
    proc := modData. procList;
    WHILE (proc # NIL) DO
      OptimizeBlock (proc. body);
      proc := proc. nextProc
    END;
    OptimizeBlock (modData. body)
  END OptimizeModule;

(* ... not supported yet
PROCEDURE OptimizeProgram (progData: Program);
  VAR
    mod: Module;
  BEGIN
    (* global optimizations can be placed here, or after the module based 
       ones ... *)
    mod := progData. moduleList;
    WHILE (mod # NIL) DO
      OptimizeModule (mod);
      mod := mod. nextModule
    END
  END OptimizeProgram;
*)

PROCEDURE DeleteGreg (VAR greg: D.GlobalRegion; VAR obj: D.Object;
                      keepInterface: BOOLEAN);
(* Deletes the GSA code in `greg' and sets `obj' to NIL if `keepInterface' is
   FALSE.  Otherwise deletes all instructions in `greg' with the exception of
   the enter and exit instructions and leaves `obj' as it is.  *)
  VAR
    instr, next: D.Instruction;
    opnd: D.Opnd;
  BEGIN
    IF keepInterface THEN
      IF (greg # NIL) THEN
        (* move enter and exit instruction into greg *)
        instr := greg. EnterInstr();
        greg. MoveInstruction (instr);
        instr := greg. ExitInstr();
        IF (instr # NIL) THEN
          greg. MoveInstruction (instr);
          (* get rid of operand arguments, but keep location attributes *)
          opnd := instr. opndList;
          WHILE (opnd # NIL) DO
            opnd. ReplaceOperand (D.constUndef);
            opnd := opnd. nextOpnd
          END
        END;
        (* delete all instructions except enter and exit *)
        instr := greg. instrList;
        WHILE (instr # NIL) DO
          next := instr. nextInstr;
          IF (instr. opcode # Opc.enter) & (instr. opcode # Opc.exit) THEN
            instr. Delete()
          END;
          instr := next
        END
      END
    ELSE
      IF (greg # NIL) THEN
        greg. bodyOf := NIL;
        greg. Delete()
      END;
      obj. greg := NIL;
      greg := NIL;
      obj := NIL
    END
  END DeleteGreg;


PROCEDURE InitializeModule (w: TextRider.Writer; 
                            obj: D.Object; tdList: D.Struct);
  BEGIN
    (* emit initialization of module data *)
    GenDecl.NewLine (w, 1);
    w. WriteString ("_mid = _register_module(&");
    w. WriteString (obj. beInfo(SystemFlags.Info). name^);
    w. WriteString ("_md.md, ");
    IF (tdList = NIL) THEN
      w. WriteString ("NULL")
    ELSE
      w. WriteChar ("&");
      GenDecl.TypeDescrName (w, tdList, TRUE);
      w. WriteString (".td")
    END;
    w. WriteString (");")
  END InitializeModule;


PROCEDURE TranslateGreg (w: TextRider.Writer; greg: D.GlobalRegion;
                         tdList: D.Struct);
(* Takes a global region in GSA form an translates it into valid (if ugly) 
   C code.  
   ... Procedure destroys GSA data structure (only enter and exit instructions
       are restored); has to be changed when procedure inlining is 
       implemented: create copy if procedure is candidate for inlining and 
       translate=procedure *)

  PROCEDURE AdjustBranchConditions (r: D.Region);
  (* Adjust branch instructions and their boolean conditions in such a way,
     that the use of negation operators in the generated "if (..) goto ..;"
     sequences is minimized.  This destroys the integrety of the GSA code, but
     this is ok since its one of the last steps of code generation and noone
     else works on the code.  *)
    VAR
      ropc, bopc: INTEGER;
    
    PROCEDURE SingleUse (u: D.Usable): BOOLEAN;
    (* Returns TRUE if `u' is only used in a single active instruction.  *)
      VAR
        use: D.Opnd;
        count: INTEGER;
        instr: D.Instruction;
      BEGIN
        count := 0;
        use := u. useList;
        WHILE (use # NIL) & (count <= 1) DO
          instr := use. instr;
          IF (instr IS D.Guard) THEN
            (* check the `no output' flag of the branch, not the one of the 
               guard itself *)
            instr := instr(D.Region). instrList
          END;
          IF ~(Classify.instrNoOutput IN instr. flags) OR 
             (instr. opcode = Opc.gate) THEN
            INC (count)
          END;
          use := use. nextUse
        END;
        RETURN (count = 1)
      END SingleUse;
    
    PROCEDURE NegateInstruction (instr: D.Instruction): BOOLEAN;
    (* If possible change the instruction opcode to evaluate to the inverse
       result, and return TRUE.  Otherwise don't change anything and return
       FALSE.  *)
      VAR
        class, subclass: INTEGER;
      BEGIN
        class := instr. opcode DIV Opc.sizeClass;
        CASE class OF
        | Opc.classEql: class := Opc.classNeq
        | Opc.classNeq: class := Opc.classEql
        | Opc.classLss: class := Opc.classGeq
        | Opc.classGtr: class := Opc.classLeq
        | Opc.classLeq: class := Opc.classGtr
        | Opc.classGeq: class := Opc.classLss
        ELSE  (* no change *)
          RETURN FALSE
        END;
        subclass := instr. opcode MOD Opc.sizeClass;
        instr. opcode := class*Opc.sizeClass + subclass;
        RETURN TRUE
      END NegateInstruction;
    
    BEGIN
      ropc := r. opcode;
      bopc := r. instrList. opcode;
      IF ((ropc = Opc.guardTrue) OR (ropc = Opc.guardFalse)) &
         ~(Classify.instrNoOutput IN r. instrList. flags) &
         ((bopc = ControlFlow.branchOnFalse) & (ropc = Opc.guardTrue) OR
          (bopc = ControlFlow.branchOnTrue) & (ropc = Opc.guardFalse)) &
         (r. opndList. arg IS D.Instruction) &
         SingleUse (r. opndList. arg) &
         NegateInstruction (r. opndList. arg(D.Instruction)) THEN
        IF (bopc = ControlFlow.branchOnFalse) THEN
          r. instrList. opcode := ControlFlow.branchOnTrue
        ELSE
          r. instrList. opcode := ControlFlow.branchOnFalse
        END
      END;
      
      r := r. regionList;
      WHILE (r # NIL) DO
        AdjustBranchConditions (r);
        r := r. nextRegion
      END
    END AdjustBranchConditions;
  
  PROCEDURE ResetLocations (enter, exit: D.Instruction);
  (* Cleanup enter and exit instructions, since the front-end will rely on this
     information when parsing the following procedures.  *)
    VAR
      res: D.Result;
      opnd: D.Opnd;
    BEGIN
      res := enter;
      WHILE (res # NIL) DO
        IF (res. location # NIL) & (res. location IS Allocate.Location) THEN
          res. location := res. location(Allocate.Location). old
        END;
        res := res. nextResult
      END;
      
      IF (exit # NIL) THEN
        opnd := exit. opndList;
        WHILE (opnd # NIL) DO
          IF (opnd. location # NIL) & (opnd. location IS Allocate.Location) THEN
            opnd. location := opnd. location(Allocate.Location). old
          END;
          opnd := opnd. nextOpnd
        END
      END
    END ResetLocations;

  BEGIN
    (* 1st step: back-end specific code transformations *)
    (* ... none yet *)
    
    (* 2nd step: classify instructions 
       Every instruction is examined to decide if it contributes to the emitted
       C code, and to which `register' file (if any) it writes its result.  *)
    Classify.Region (greg);
    
    (* 3rd step: instruction scheduling
       The half-ordering of GSA code is turned into a strict sequence of 
       instructions.  This scheduling also makes sure that all instructions
       reading from a structured value are completed before this value is 
       changed by an update instructions.  This way the back-end is able to
       assign a single memory location to those (record, array, or complex) 
       values.  *)
    Schedule.Region (greg);

    (* 4th step: assign location attributes 
       For every result and every operand the final location is determined.  
       For a back-end emitting machine code this will assign register to the
       operands and results of instructions, and insert spill code at the 
       appropriate places if the register file isn't large enough to hold all
       live values.  The C back-end does a similar thing, although it works
       with `pseudo' registers, i.e. variables of the basic types int, float, 
       and double.  *)
    Allocate.GlobalRegion (greg);
    Allocate.EmitVariables (w, greg, GenStatm.valueStack. value >= 0);
(*    WriteGSAvC.Body (greg);  (* note: enabling GSA output changes label ids *)*)
    
    (* 5th step: transform control flow information
       Jump and branch instructions are added to the GSA code.  They represent
       the flow of control between guards and merges in the way required by
       assembler code.  CAUTION: This transformation severly changes the
       structure of the GSA code by adding instructions with non-standard 
       semantics and moving merge regions around.  Most of the procedures 
       gathering information from GSA won't work after this.  *)
    ControlFlow.GlobalRegion (greg);
    AdjustBranchConditions (greg);
    WriteGSAvC.Body (greg);  (* note: enabling GSA output changes label ids *)
    
    (* 6th step: emit C statements 
       At last C statements are emitted.  Instructions are written in a single
       pass over the given global region.  This is a simple inorder traversal
       of the GSA hierarchie.  *)
    GenStatm.SetWriter (w);
    IF (greg. bodyOf. mode = D.objModule) THEN
      InitializeModule (w, greg. bodyOf, tdList)
    ELSE
      GenStatm.EmitLocalVars (greg. bodyOf. localDecl)
    END;
    GenStatm.GlobalRegion (greg);
    
    (* 7th step: cleanup data in enter and exit instructions 
       With translation on a per procedure basis, the front-end will use 
       some data of previously translated procedures, most notably the enter
       and exit instructions and, with procedure inlining enabled, the whole
       procedure body.  Therefore those parts of the GSA code that are used
       later mustn't be destroyed by the back-end and have to returned to the
       state that the front-end expects.  *)
    ResetLocations (greg. EnterInstr(), greg. ExitInstr())
  END TranslateGreg;


PROCEDURE EmitProcedure (w: TextRider.Writer; proc: Procedure);
  VAR
    fpar: D.Object;
  BEGIN
    IF (w # NIL) THEN
      (* dependence analysis should provide information to
         avoid unnecessary copies of value parameters *)
      fpar := proc. obj. type. decl;
      WHILE (fpar # NIL) DO
        IF (StdTypes.objLocalCopy IN fpar. beFlags) &
           ~AliasAnalysis.NeedLocalCopy (proc. body, fpar) THEN
          EXCL (fpar. beFlags, StdTypes.objLocalCopy)
        END;
        fpar := fpar. rightObj
      END;

      GenDecl.Declaration (w, proc. obj, 
             {GenDecl.function, GenDecl.doNotMark, GenDecl.ignoreUsedDecl}, 0);
      w. WriteString (" {");
      TranslateGreg (w, proc. body, NIL);
      GenDecl.NewLine (w, 0);
      w. WriteChar ("}");
      GenDecl.NewLine (w, 0)
    END
  END EmitProcedure;

PROCEDURE EmitModuleBody (w: TextRider.Writer; modData: Module; 
                          tdList: D.Struct);
  BEGIN
    IF (w # NIL) THEN
      w. WriteLn;
      w. WriteString ("void ");
      w. WriteString (modData. obj. beInfo(SystemFlags.Info). name^);
      w. WriteString ("_init(void) {");
      (* emit module body *)
      TranslateGreg (w, modData. body, tdList);
      w. WriteLn;
      w. WriteChar ("}");
      w. WriteLn
    END
  END EmitModuleBody;

PROCEDURE EmitDeclarations (w: TextRider.Writer; objList: GenDecl.ObjectList;
                            objCount: LONGINT; mod: Module;
                            header: BOOLEAN);
(* This procedure generates the declarations the make up the header file and
   the file with global declarations (.d).  *)
  VAR
    flags: SET;
    i, j, lenInit, filledInit: LONGINT;
    obj: D.Object;
    s: Sym.StructList;
    init: GenConst.UpdateList;
    copy: D.Instruction;
    
  PROCEDURE CollectInitialization (obj: D.Object; 
                                   VAR list: GenConst.UpdateList;
                                   VAR lenList, filled: LONGINT);
  (* Checks whether `obj' denotes a array variable and collects all constant
     declarations into `list'.  If `obj' isn't an array, or it isn't 
     initialized with constant values (constant both for index and and element
     value), or the init table would be too large, `list' will be set to NIL.
     Otherwise it refers to a list of update instructions that can be fed to
     `GenConst.EmitIntialization'.  `lenList' is the first unused index, 
     `filled' the number of defined indices (0 <= filled <= lenList).  *)
    VAR
      greg: D.GlobalRegion;
      use: D.Opnd;
      
    PROCEDURE AddElement (index: LONGINT; update: D.Instruction);
      VAR
        new: GenConst.UpdateList;
        i, len, oldLen: LONGINT;
      BEGIN
        (* make sure that the array is large enough *)
        IF (list = NIL) OR (index >= LEN (list^)) THEN
          IF (list = NIL) THEN
            len := 64;
            oldLen := 0
          ELSE
            len := LEN (list^);
            oldLen := len
          END;
          WHILE (len < index+1) DO
            len := len*2
          END;
          NEW (new, len);
          IF (list # NIL) THEN
            FOR i := 0 TO LEN (list^)-1 DO
              new[i] := list[i]
            END
          END;
          FOR i := oldLen TO len-1 DO
            new[i] := NIL
          END;
          list := new
        END;
        
        IF (list[index] = NIL) THEN
          INC (filled)
        END;
        list[index] := update;
        IF (lenList <= index) THEN
          lenList := index+1
        END
      END AddElement;
    
    PROCEDURE TraceUpdates (value: D.Usable; offset: LONGINT; type: D.Struct);
    (* Collect all (constant index, constant value) pairs for the given
       variable.  `value' is the chain that is used to reach all relevant 
       updates, `offset' the index relative to which the next update is
       interpreted, and `type' the type description of the array type.  *)
      CONST
        maxIndex = 1024*1024-1;
      VAR
        use: D.Opnd;
        instr: D.Instruction;
        index, const: D.Usable;
        t: D.Struct;
        elems, i: LONGINT;
        region: D.Region;
      
      PROCEDURE Elements (t: D.Struct): LONGINT;
        BEGIN
          IF (t. form = D.strArray) THEN
            RETURN t. len * Elements (t. base)
          ELSE
            RETURN 1
          END
        END Elements;
      
      BEGIN
        ASSERT (type. form = D.strArray);
        use := value. useList;
        WHILE (use # NIL) DO
          instr := use. instr;
          IF (instr. opcode # Opc.accessElement) & 
             (instr. opcode # Opc.updateElement) THEN
            (* ignore all other instructions *)
          ELSIF (instr. region # greg) THEN  (* check place of instruction *)
            region := instr. region;
            WHILE (region. region # NIL) DO
              region := region. region
            END;
            IF (region = greg) THEN
              (* ignore uses in other procedures, but abort if be are in a
                 nested region of the current greg; we might end up in other
                 gregs when searching the use list of the global variable *)
              RETURN
            END
          ELSIF (instr.opcode = Opc.updateElement) & (use.nextOpnd = NIL) THEN
            (* `use' is last operand of the instruction; both `type' and
               `offset' have to be turned back one step *)
            t := obj. type;
            WHILE (t. base # type) DO
              t := t. base
            END;
            elems := Elements (t);
            TraceUpdates (instr, (offset DIV elems)*elems, t)
          ELSIF (use # use. instr. opndList) OR
                ~(instr. NthArgument (2) IS D.Const) THEN
            (* ignore if not first operand, or index isn't constant *)
            RETURN
          ELSIF (instr. opcode = Opc.updateElement) THEN
            const := instr. NthArgument (3);
            IF (const IS D.Const) THEN
              index := instr. NthArgument (2);
              i := offset+index(D.Const). int;
              IF (i >= maxIndex) OR
                 (list # NIL) & (i < LEN (list^)) & (list[i] # NIL) THEN
                (* abort if index is above an arbitrary bound or if there is 
                   already a value assigned to the given index *)
                RETURN
              ELSE
                AddElement (offset+index(D.Const). int, instr);
                TraceUpdates (instr, offset, type)
              END
            END
          ELSIF (instr. opcode = Opc.accessElement) & 
                (type. base. form = D.strArray) THEN
            const := instr. NthArgument (2);
            TraceUpdates (instr, 
                          offset+const(D.Const). int*Elements (type. base),
                          type. base)
          END;
          use := use. nextUse
        END
      END TraceUpdates;
      
    BEGIN
      list := NIL;
      lenList := 0;
      filled := 0;
      IF (obj. mode = D.objVar) & (obj. type. form = D.strArray) THEN
        greg := mod. body;
        use := obj. useList;
        WHILE (use # NIL) DO
          IF (use.  instr. region = greg) & 
             (use. instr. opcode = Opc.zero) THEN
            (* the variable is initialized by this "zero" instruction; follow
               its tracks to get the initalization; if we are successful 
               get rid of the thing or it´ll zero out all our efforts *)
            TraceUpdates (use. instr, 0, obj. type);
            IF (list # NIL) THEN
              use. instr. ReplaceUses (obj);
              use. instr. Delete()
            END;
            RETURN
          END;
          use := use. nextUse
        END;
        (* array isn´t initialized with a `zero´ instruction, track the 
           updates applied to the "undefined value" represented by `obj´ *)
        TraceUpdates (obj, 0, obj. type)
      END
    END CollectInitialization;
  
  PROCEDURE RemoveNoopUpdates (value: D.Usable; greg: D.GlobalRegion);
  (* After all element updates have been moved into the variable's init 
     expression, a number of indermediate updates is left behind for 2 or
     higher dimensional arrays.  This ugly hack gets rid of them.  *)
    VAR
      use, use2: D.Opnd;
      instr, instr2: D.Instruction;
      noChange: BOOLEAN;
    BEGIN
      REPEAT
        noChange := TRUE;
        use := value. useList;
        WHILE (use # NIL) DO
          instr := use. instr;
          IF (instr. region = greg) &
             (instr. opcode = Opc.accessElement) & 
             (instr. opndList = use) &
             Sym.TypeInGroup (instr. type, D.grpStructured) THEN
            RemoveNoopUpdates (instr, greg);
            use2 := instr. useList;
            WHILE (use2 # NIL) DO
              instr2 := use2. instr;
              IF (instr2. region = greg) &
                 (instr2. opcode = Opc.updateElement) & 
                 (use2. nextOpnd = NIL) &
                 (instr. opndList. arg = instr2. opndList. arg) &
                 (instr. NthArgument (2) = instr2. NthArgument (2)) THEN
                (* the update `instr2' is a noop, it stores the value obtained
                   from the same position *)
                instr2. ReplaceUses (instr2. opndList. arg);
                instr2. Delete();
                noChange := FALSE
              END;
              use2 := use2. nextUse
            END
          END;
          use := use. nextUse
        END
      UNTIL noChange;
    END RemoveNoopUpdates;
  
  BEGIN
    FOR i := 0 TO objCount-1 DO
      obj := objList[i];
      IF (obj. mode # D.objModule) & 
         ((obj. mode # D.objConst) OR header) &
         ((obj. mode # D.objProc) OR header) &
         ((header = (D.objInSymbolFile IN obj. flags)) OR
          ~header & ~(StdTypes.objEmitted IN obj. beFlags)) THEN
        (* no module or constant declarations are emitted (except string 
           constants); no procedure declarations are put into the .d file;
           only exported declarations are put into the header file; 
           if the previous pass only wrote a declaration, but not the
           definition of `obj', then write it again *)
        flags := {};
        IF (obj. mode = D.objProc) THEN  
          (* note: tb procs don't appear as global declarations *)
          flags := flags + {GenDecl.function, GenDecl.prototype}
        END;
        
        IF header THEN
          INCL (flags, GenDecl.external)
        ELSIF ~(D.objIsExported IN obj. flags) &
              ((obj. mode = D.objVar) & (obj. level = Sym.globalLevel) OR
               (obj. mode = D.objProc)) THEN
          INCL (flags, GenDecl.static)
        END;
        
        (* prepare for extraction of array initialization *)
        IF header THEN
          init := NIL
        ELSE
          CollectInitialization (obj, init, lenInit, filledInit);
          IF (lenInit > 10) & (filledInit < lenInit DIV 4) THEN
            (* forget initialization if the defined places are sparse *)
            init := NIL
          END;
          IF (init # NIL) THEN
            INCL (flags, GenDecl.noSemicolon)
          END
        END;
        
        GenDecl.Declaration (w, obj, flags, 0);
        
        IF (init # NIL) THEN
          (* create copy of undefined value *)
          copy := mod. body. CreateInstruction (Opc.copy, obj. type, D.undefPos);
          copy. Operand (obj);
          
          (* emit array initialization and remove update instructions *)
          GenConst.EmitInitialization (w, obj, init, lenInit);
          FOR j := 0 TO lenInit-1 DO
            IF (init[j] # NIL) THEN
              IF (init[j]. opndList. arg = obj) THEN
                init[j]. ReplaceUses (copy)
              ELSE
                init[j]. ReplaceUses (init[j]. opndList. arg)
              END;
              init[j]. Delete();
              init[j] := NIL
            END
          END;
          (* get rid of any intermediate update instructions *)
          RemoveNoopUpdates (obj, mod. body);
          DeadCodeElimination.Eliminate (mod. body, FALSE)
        END
      END
    END;
    
    (* also write declarations for structured types declared inside 
       procedures *)
    s := mod. structList;
    WHILE (s # NIL) DO
      IF (header = (s. type. obj # NIL) & 
                   (D.objIsExported IN s. type. obj. flags)) THEN
        GenDecl.TypeDeclaration (w, s. type, {}, 0)
      END;
      s := s. next
    END
  END EmitDeclarations;

PROCEDURE EmitHeaderFile (w: TextRider.Writer; mod: Module);
  VAR
    s: Sym.StructList;
    proc: Procedure;
  BEGIN
    w. WriteString ("#ifndef _MODULE_");
    w. WriteString (mod. obj. beInfo(SystemFlags.Info). name^);
    w. WriteString ("_");
    w. WriteLn;
    w. WriteString ("#define _MODULE_");
    w. WriteString (mod. obj. beInfo(SystemFlags.Info). name^);
    w. WriteString ("_");
    w. WriteLn;
    EmitDeclarations (w, GenDecl.objList, GenDecl.objCount, mod, TRUE);
                      
    (* write prototypes for type-bound procedures *)
    proc := mod. procList;
    WHILE (proc # NIL) DO
      IF (proc. obj. mode = D.objTBProc) THEN
        GenDecl.Declaration (w, proc. obj, 
          {GenDecl.function, GenDecl.prototype, GenDecl.external}, 0)
      END;
      proc := proc. nextProc
    END;
    
    (* write declarations of type descriptors *)
    s := mod. structList;
    WHILE (s # NIL) DO
      IF (s. type. form = D.strRecord) THEN
        GenDecl.TypeDescriptor (w, mod. obj, s. type, NIL, TRUE)
      END;
      s := s. next
    END;
    
    (* write prototype of initialization function *)
    IF (StdTypes.objInitFct IN mod. obj. beFlags) THEN 
      w. WriteLn;
      w. WriteString ("extern void ");
      w. WriteString (mod. obj. beInfo(SystemFlags.Info). name^);
      w. WriteString ("_init(void);")
    END;
    w. WriteLn;
    w. WriteLn;
    w. WriteString ("#endif");
    w. WriteLn
  END EmitHeaderFile;

PROCEDURE EmitTypeDescriptors (w: TextRider.Writer; mod: Module): D.Struct;
  VAR
    s: Sym.StructList;
    last: D.Struct;
  BEGIN
    w. WriteLn; w. WriteString ("/* module and type descriptors */");
    GenDecl.ModuleDescriptor (w, mod. obj);
    s := mod. structList;
    last := NIL;
    WHILE (s # NIL) DO
      IF ~(StdTypes.structTDEmitted IN s. type. beFlags) &
         (s. type. form = D.strRecord) THEN
        GenDecl.TypeDescriptor (w, mod. obj, s. type, last, FALSE);
        last := s. type
      END;
      s := s. next
    END;
    
    IF (translationBasis. value^ = translateGlobProc) THEN
      GenDecl.PatchTBCalls (w)
    END;
    
    w. WriteLn; w. WriteLn; 
    RETURN last
  END EmitTypeDescriptors;
  
PROCEDURE EmitDeclFile (w: TextRider.Writer; mod: Module);
  PROCEDURE WriteOtherImports (obj: D.Object);
    VAR
      importedMod: D.Object;
    BEGIN
      IF (obj # NIL) THEN
        WriteOtherImports (obj. leftObj);
        IF (obj. mode = D.objModule) THEN
          importedMod := SymbolFile.FindImportedModule (obj. data(D.Const). string^);
          IF ~(StdTypes.objIncluded IN importedMod. beFlags) THEN
            GenInclude.Include (w, importedMod, ".h", FALSE)
          END
        END;
        WriteOtherImports (obj. rightObj)
      END
    END WriteOtherImports;
  
  PROCEDURE EmitPrototypes (w: TextRider.Writer; procList: Procedure);
    VAR
      proc: Procedure;
    BEGIN
      proc := procList;
      WHILE (proc # NIL) DO
        IF (StdTypes.objNeedPrototype IN proc. obj. beFlags) THEN
          GenDecl.Declaration (w, proc. obj, 
                               {GenDecl.function, GenDecl.prototype}, 0)
        END;
        proc := proc. nextProc
      END
    END EmitPrototypes;
  
  BEGIN  
    IF (w # NIL) THEN
      GenInclude.Include (w, mod. obj, ".h", TRUE);
      WriteOtherImports (mod. obj. localDecl);
      w. WriteLn; w. WriteLn;
      w. WriteString ("/* local definitions */");
      EmitDeclarations (w, GenDecl.objList, GenDecl.objCount, mod, FALSE);
      w. WriteLn; w. WriteLn;
      w. WriteString ("/* function prototypes */");
      EmitPrototypes (w, mod. procList);
      w. WriteLn
    END
  END EmitDeclFile;



PROCEDURE WriteSymbolFile (modData: Module);
(* Generates and registers the symbol file of `modData. obj'.  The module's
   exported objects are transfered to the data structure that holds all 
   imported symbol files.
   pre: E.noerr & (translationBasis. value^ # translateProgram) *)
  VAR
    newSym, changedSym: BOOLEAN;
  BEGIN
    SymbolFile.Write (modData. obj, newSym, changedSym);
    modData. symbolFileMagic := modData. obj. data(D.Const). int;
    IF newSym THEN
      E.VerboseMsg ("   new symbol file")
    END;
    IF changedSym THEN
      E.VerboseMsg ("   symbol file changed")
    END
  END WriteSymbolFile;


PROCEDURE CreateProgram* (buildLib: External.Lib): Program;
(* Allocates the data structure structure to hold all information of the 
   program.  Usually this information is a list of all imported modules, but 
   the back-end can place arbitrary data here.  Called as part of a `make' 
   which passes the result to the parser, which in turn uses it for first 
   operand when calling `FinishModule' or `AddModule'.  *)
  VAR
    progData: Program;
  BEGIN
    NEW (progData);
    progData. moduleList := NIL;
    progData. buildLib := buildLib;
    RETURN progData
  END CreateProgram;

PROCEDURE CreateModule* (progData: Program; modObj: D.Object): Module;
(* Allocates the data structure structure to hold all information of the 
   module and registers it in `progData' if it isn't NIL.  The value for
   `progData' was created by a previous call to `CreateProgram'.  `modObj' is 
   the symbol table entry of the module, containing all local declarations.  
   This procecure is called from `ParseDecl.Module' as soon as the module 
   header is parsed, but before the import list.  *)
  VAR
    modData: Module;
    
  PROCEDURE CreateFiles (mod: D.Object);
    PROCEDURE CreateTmpFile (fd: FileData.FileData): TextRider.Writer;
      VAR
        f: Files.File;
        res: Files.Result;
        msg: ARRAY 256 OF CHAR;
      BEGIN
        f := Files.Tmp (fd. filename^, {Files.write}, res);
        IF (f = NIL) THEN
          res. GetText (msg);
          E.FileError ("Couldn't create file `%'", fd. filename^, msg)
        END;
        RETURN TextRider.ConnectWriter (f)
      END CreateTmpFile;
      
    BEGIN
      (* create header file *)
      hFile := FileData.NewFile (mod. name^, ".h");
      hWriter := CreateTmpFile (hFile);
      hWriter. WriteString (Build.msgGenerated); hWriter. WriteLn;
      
      (* create code and declaration file, unless the module is an interface to
         an existing piece of code without any code of its own *)
      IF (StdTypes.objCodeFile IN mod. beFlags) THEN
        dFile := FileData.NewFile (mod. name^, ".d");
        cFile := FileData.NewFile (mod. name^, ".c");
        dWriter := CreateTmpFile (dFile);
        cWriter := CreateTmpFile (cFile);
        IF (progData # NIL) & (progData. buildLib # NIL) THEN
          FileData.MarkForRemoval (dFile. filename^, "");
          FileData.MarkForRemoval (cFile. filename^, "")
        END;
        dWriter. WriteString (Build.msgGenerated);
        cWriter. WriteString (Build.msgGenerated); 
    
        (* emit header of code file; the procedures will be appended to this 
           file *)
        GenInclude.IncludeFile (cWriter, "__oo2c", ".h");
        GenInclude.IncludeFile (cWriter, "__libc", ".h");
        GenInclude.Include (cWriter, mod, ".d", TRUE);
        cWriter. WriteLn;
        cWriter. WriteLn;
        cWriter. WriteString ("static _ModId _mid;");
        cWriter. WriteLn
      ELSE
        dFile := NIL; dWriter := NIL;
        cFile := NIL; cWriter := NIL
      END
    END CreateFiles;
  
  PROCEDURE AppendModule (VAR modList: Module; mod: Module);
    BEGIN
      IF (modList = NIL) THEN
        mod. nextModule := NIL;
        modList := mod
      ELSE
        AppendModule (modList. nextModule, mod)
      END
    END AppendModule;
  
  BEGIN
    NEW (modData);
    modData. obj := modObj;
    modData. symbolFileMagic := 0;
    modData. procList := NIL;
    modData. body := NIL;
    modData. structList := NIL;
    modData. progData := progData;
    IF (progData # NIL) THEN
      AppendModule (progData. moduleList, modData)
    ELSE
      modData. nextModule := NIL
    END;
    IF (modData. obj. mode > 0) THEN  (* module is actually compiled *)
      CreateFiles (modData. obj);
      GenConst.InitStringList
    (* ELSE: module info is taken from symbol file, no translation *)
    END;
    
    IF (progData # NIL) & (progData. buildLib # NIL) THEN
      (* add information to the symbol file that the linker should take this
         module from the specified library *)
      SystemFlags.CreateInfo (modObj);
      INCL (modObj. flags, D.objExportsBEInfo);
      INCL (modObj. beFlags, StdTypes.objInLibrary);
      IF (modObj. beInfo(SystemFlags.Info). library # progData. buildLib) THEN
        EXCL (modObj. beFlags, StdTypes.objLibraryMaster)
      END;
      modObj. beInfo(SystemFlags.Info). library := progData. buildLib;
    END;
    
    (* initialize list of type-bound procedure calls whose procedure index
       is not known when code is emitted for the call *)
    GenDecl.tbCallList := NIL;
    
    RETURN modData
  END CreateModule;

PROCEDURE FileMissing* (mod: Make.Module): BOOLEAN;
(* Returns TRUE if one of the files generated by the back-end for module 
   `modName' does not exist.  In this case a recompilation of `modName' will be
   necessary.  *)
  VAR
    file: FileData.FileData;
    hasCode: BOOLEAN;
  BEGIN
    hasCode := (StdTypes.objCodeFile IN mod. moduleInfo. beFlags);
    IF (StdTypes.objInLibrary IN mod. moduleInfo. beFlags) THEN
      hasCode := FALSE
    END;
    
    file := FileData.FindFile (mod. name^, ".h", FALSE);
    IF ~(FileData.fileExists IN file. flags) THEN
      RETURN TRUE
    END;
    IF hasCode THEN
      file := FileData.FindFile (mod. name^, ".d", FALSE);
      IF ~(FileData.fileExists IN file. flags) THEN
        RETURN TRUE
      END;
      file := FileData.FindFile (mod. name^, ".c", FALSE);
      RETURN ~(FileData.fileExists IN file. flags)
    ELSE
      RETURN FALSE
    END
  END FileMissing;

PROCEDURE AddModule* (progData: Program; name: ARRAY OF CHAR);
(* Called by the make loop for modules that are up to date and don't need to be
   recompiled.  `name' is the name of the (imported) module.  The module is 
   added to the program's list of modules, so that at the end of the make the
   full list of modules is stored in `progData'.  *)
  VAR
    obj: D.Object;
    modData: Module;
  BEGIN
    obj := Sym.NewObject (name, -D.objModule, D.undefPos);
    modData := CreateModule (progData, obj)
  END AddModule;

PROCEDURE FinishProcedure* (modData: Module; procObj: D.Object; 
                            body: D.GlobalRegion);
(* Called by the parser right after a procedure has been parsed.  `modData' is
   the object that was generated previously be a call to `CreateModule', 
   `procObj' the procedure's symbol table entry, and `body' the procedure's
   GSA code (ie its greg).  `body' is NIL if the procedure is a declaration of
   an external procedure.  
   pre: `Error.noerr' holds, ie no error was found until now; `procObj' is not
     a forward declaration  *)
  VAR
    proc, ptr, start: Procedure;
                      
  PROCEDURE AppendProcedure (VAR procList: Procedure; proc: Procedure);
    BEGIN
      IF (procList = NIL) THEN
        proc. nextProc := NIL;
        procList := proc
      ELSE
        AppendProcedure (procList. nextProc, proc)
      END
    END AppendProcedure;
  
  BEGIN
    NEW (proc);
    proc. obj := procObj;
    proc. body := body;
    AppendProcedure (modData. procList, proc);
    
    (* assign C names to local declarations in `proc' and to the module's
       global declarations (unless this has been done already) *)
    GenDecl.AssignNames (modData. obj);
    GenDecl.AssignNames (proc. obj);

    IF (translationBasis. value^ = translateGlobProc) &
       (procObj. level = Sym.globalLevel) & E.noerr THEN
      (* translation is done per global procedure; the code of the procedure 
         and the procedures nested in it is run through the optimizers and 
         emitted; afterwards the procedure bodies are discarded, with the 
         exception of the enter and exit instruction of the global one *)
      start := modData. procList;
      ptr := modData. procList;
      WHILE (ptr # proc) DO
        IF (ptr. obj. level = Sym.globalLevel) THEN
          start := ptr. nextProc
        END;
        ptr := ptr. nextProc
      END;
      
      (* correct side-effect information between calls of the global procedure
         `proc' and its nested procedures *)
      SideEffects.Init;
      ptr := start;
      REPEAT
        SideEffects.AddProc (ptr. body);
        ptr := ptr. nextProc
      UNTIL (ptr = NIL);
      SideEffects.Adjust;
      
      ptr := start;
      REPEAT
        IF (ptr. body # NIL) THEN
          OptimizeBlock (ptr. body);
          EmitProcedure (cWriter, ptr);
          (* get rid of the bulk of GSA code, but keep the enter and exit 
             instruction of the global procedure *)
          DeleteGreg (ptr. body, ptr. obj, TRUE)
        END;
  
        ptr := ptr. nextProc
      UNTIL (ptr = NIL)
    END
  END FinishProcedure;

PROCEDURE ForwardProcedure* (modData: Module; procObj: D.Object);
(* Called by the parser right after a forward procedure has been parsed.  
   `modData' is the object that was generated previously be a call to 
   `CreateModule', `procObj' the procedure's symbol table entry.  Note that
   `procObj' will be assigned to the actual definition of the procedure later 
   on, i.e. forward declaration and actual definition share the same symbol 
   table entry.
   pre: `Error.noerr' holds, i.e. no error was found until now  *)
  BEGIN
    (* assign C names to local declarations in `proc' and to the module's
       global declarations (unless this has been done already) *)
    GenDecl.AssignNames (modData. obj);
    GenDecl.AssignNames (procObj)
  END ForwardProcedure;
                            
PROCEDURE FinishModule* (modData: Module; body: D.GlobalRegion;
                         structList: Sym.StructList);
(* Called by the parser when the module has been parsed completely.  `modData'
   is the object that was generated previously be a call to `CreateModule', 
   `body' the module's GSA code (ie its greg).   `structList' is a list 
   containing all structured (ie, ARRAY and RECORD) type constructors of the
   module.  With `keepModuleObj=FALSE' the reference to the module's symbol
   table in `modData.obj' is set to NIL, allowing the garbage collector to 
   free it.
   pre: `Error.noerr' holds, ie no error was found until now.  *)
  VAR
    mod: D.Object;
    proc: Procedure;
    tdList: D.Struct;
    keepModuleObj: BOOLEAN;
    
  PROCEDURE CloseFile (w: TextRider.Writer; fd: FileData.FileData);
    VAR
      f: Files.File;
      msg: ARRAY 256 OF CHAR;
    BEGIN
      IF (w. res # TextRider.done) THEN
        w. res. GetText (msg);
        E.FileError ("Write error in file `%'", fd. filename^, msg)
      END;
      f := w. base(Files.File);
      IF E.noerr THEN
        f. Register;
        IF (f. res # Files.done) THEN
          f. res. GetText (msg);
          E.FileError ("Registering file `%' failed", fd. filename^, msg)
        END;
      END;
      f. Close;
      IF (f. res # Files.done) THEN
        f. res. GetText (msg);
        E.FileError ("Closing file `%' failed", fd. filename^, msg)
      END
    END CloseFile;
  
  BEGIN
    modData. body := body;
    modData. structList := structList;
    keepModuleObj := (modData. progData # NIL) &
                     (modData. progData. buildLib # NIL);
    
    IF (translationBasis. value^ # translateGlobProc) THEN
      (* fix side-effect information of recursive calls *)
      SideEffects.Init;
      proc := modData. procList;
      WHILE (proc # NIL) DO
        SideEffects.AddProc (proc. body);
        proc := proc. nextProc
      END;
      SideEffects.Adjust
    END;
    
    (* assign C names to the module's global declarations unless this has 
       already been done *)
    GenDecl.AssignNames (modData. obj);

    IF (translationBasis. value^ = translateModule) THEN
      (* translation is done per module; all declarations and procedures are
         collected before any optimization is done; compilation to target code
         happens in a single step after all optimizations have been run *)
      IF E.noerr THEN
        OptimizeModule (modData);
        
        IF E.noerr THEN
          (* write symbol file (unless the optimizers found an error) *)
          WriteSymbolFile (modData);
          
          (* emit code; in this case this means to write a textual
             representation of the intermediate GSA code to stdout (and to 
             update the instruction counter if statistics are enabled) *)
          proc := modData. procList;
          WHILE (proc # NIL) DO
            EmitProcedure (cWriter, proc);
            proc := proc. nextProc
          END
        END
      END
    ELSIF (translationBasis. value^ = translateGlobProc) THEN
      IF E.noerr THEN
        WriteSymbolFile (modData);
        
        (* emit module body, the procedures have already been handled by 
           `FinishProcedure' *)
        OptimizeBlock (modData. body)
      END
    (* ELSE: (translationBasis. value^ = translateProgram)
       no symbol file is written, instead move the whole symbol information
       of the current module into the data structure that holds the the
       imported modules; as a side-effect the enter/exit information of
       procedures is available for importing modules *)
    END;
    
    IF E.noerr & (translationBasis. value^ # translateProgram) THEN
      GenDecl.BuildObjList (modData. obj);
      (* clear `objImported' markers for all modules *)
      mod := Sym.importedMods;
      WHILE (mod # NIL) DO
        EXCL (mod. beFlags, StdTypes. objIncluded);
        mod := mod. rightObj
      END;
      EmitHeaderFile (hWriter, modData);
      EmitDeclFile (dWriter, modData);
      IF (dWriter # NIL) THEN
        tdList := EmitTypeDescriptors (dWriter, modData)
      ELSE
        tdList := NIL
      END;
      EmitModuleBody (cWriter, modData, tdList);
      IF (dWriter # NIL) THEN
        dWriter. WriteString ("/* local strings */");
        GenDecl.Strings (dWriter, GenConst.stringList);
        dWriter. WriteLn; dWriter. WriteLn
      END;
    END;
    
    (* transfer exported symbols of the current module into the list of
       imported symbols (this avoids to read the symbol file if this module
       is imported in the next compilation); if we aren't translating per 
       program, then delete all not exported symbols and local declarations of
       procedures *)
    SymbolFile.IntegrateSymbols (modData. obj, 
                          translationBasis. value^ # translateProgram);

    IF (translationBasis. value^ # translateProgram) THEN
      (* delete procedure information and GSA code associated with the 
         current module; this is necessary for the gc to find collectable 
         blocks *)
      WHILE (modData. procList # NIL) DO
        DeleteGreg (modData. procList. body, modData. procList. obj, FALSE);
        modData. procList := modData. procList. nextProc
      END;
      DeleteGreg (modData. body, modData. obj, keepModuleObj);
      modData. structList := NIL;
      
      (* register files unless an error was found *)
      CloseFile (hWriter, hFile);
      IF (cFile # NIL) THEN
        CloseFile (dWriter, dFile);
        CloseFile (cWriter, cFile)
      END
    END;
    D.FreeConsts  (* free unused constant objects *)
  END FinishModule;

PROCEDURE FinishProgram* (progData: Program);
(* Called by the compiler when all modules of a make have been compiled.
   `progData' is the object that was generated previously be a call to 
   `CreateProgram'.  All modules have been inserted by previous calls to 
   `FinishModule' and `AddModule', so that `progData. moduleList' holds a
   full set of imported modules in a valid initialization sequence for their 
   bodies.
   pre: `Error.noerr' holds, ie no error was found until now.  *)
(* ... not supported yet  
  VAR
    mod: Module;
    proc: Procedure;
  BEGIN
    IF (translationBasis. value^ = translateProgram) THEN
      OptimizeProgram (progData);
      
      mod := progData. moduleList;
      WHILE (mod # NIL) DO
        proc := mod. procList;
        WHILE (proc # NIL) DO
          EmitProcedure (cWriter, proc);
          proc := proc. nextProc
        END;
        EmitModuleBody (cWriter, mod);
        mod := mod. nextModule
      END
    END
*)
  END FinishProgram;


BEGIN
  translationBasis := ParamOptions.CreateString ("translationBasis", 
                                                 translationDefault);
  ParamOptions.options. CmdLineOption ("--translate", "translationBasis:='$1'");
  ParamOptions.options. Add (translationBasis);
  
  stupidCodeGen := ParamOptions.CreateBoolean ("stupidCodeGen", FALSE);
  ParamOptions.options. Add (stupidCodeGen);
  ParamOptions.options. CmdLineOption ("--stupid", "stupidCodeGen:=TRUE");
  
  optimizers := ParamOptions.CreateString ("optimizers", useDefaultOpt);
  ParamOptions.options. CmdLineOption ("--opt", "optimizers:='$1'");
  ParamOptions.options. Add (optimizers);
  
  checks := ParamOptions.CreateBoolean ("checks", FALSE);
  ParamOptions.options. CmdLineOption ("--checks", "checks:=TRUE");
  ParamOptions.options. Add (checks);
  
  InstallOptimizers
END CodeGen.
