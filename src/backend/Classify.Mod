(*	$Id: Classify.Mod,v 1.27 1999/05/20 20:31:31 acken Exp $	*)
MODULE Classify;
(*  Classifies GSA instruction with respect to their translation to ANSI-C.
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
  D := Data, Opc := Opcode, Sym := SymbolTable;
  
CONST
  prefixInt* = "i";
  prefixHuge* = "h";
  prefixReal* = "f";
  prefixLongReal* = "d";
  prefixAuxiliary* = "a";
  
CONST  
  (* list of instruction categories; categories are stored in 
     `Instruction.flags' *)
  instrNoOutput* = D.minInstrFlag;
  (* this instruction does not constribute to the emitted C code in form of a
     statement; either because it's only needed to keep the GSA code 
     consistent, or because it has only meaning together with another 
     instruction whose generated code will incorporate this instruction's
     information *)
  instrVoid* = D.minInstrFlag+1;
  (* instruction is translated to statement *)
  instrInt* = D.minInstrFlag+2;
  (* instruction puts its result into the `integer' register file *)
  instrHuge* = D.minInstrFlag+3;
  (* instruction puts its result into the `huge integer' register file *)
  instrReal* = D.minInstrFlag+4;
  (* instruction puts its result into the `single precision real' register 
     file *)
  instrLongReal* = D.minInstrFlag+5;
  (* instruction puts its result into the `double precision real' register 
     file *)
  instrDelayedRegion* = D.minInstrFlag+6;
  (* used in Schedule.Schedule; marks a region that is merged into another 
     region and is therefore always scheduled as part of its merge *)
  instrJumpTarget* = D.minInstrFlag+7;
  (* instruction is target of a goto *)
  instrSpecialDecl* = D.minInstrFlag+8;
  (* the greg has to insert additional declarations for some special code 
     procedures appearing in its code *)
  
  backendFlags = {instrNoOutput..instrSpecialDecl};
  (* mask with all flags set by the back-end *)
  
CONST
  spPushContext* = 1;
  
  
(* Some helpful functions to deal with update/access instructions: *)
  
PROCEDURE ElementUpdate* (arg: D.Usable): BOOLEAN;
  BEGIN
    RETURN (arg IS D.Instruction) &
           ((arg(D.Instruction). opcode = Opc.updateField) OR
            (arg(D.Instruction). opcode = Opc.updateElement))
  END ElementUpdate;

PROCEDURE NoopUpdate* (instr: D.Instruction): BOOLEAN;
(* Returns TRUE iff the given update `instr' merely passes the effects of of
   another update or a procedure call along, without changing something in 
   memory itself.  Such an instruction doesn't have to be translated into 
   target code, it's a "no operation".
   pre: instr. opcode DIV sizeClass = Opc.classUpdate *)
  VAR
    inOpnd: D.Opnd;
    
  PROCEDURE SideEffect (res: D.Result): BOOLEAN;
  (* Return TRUE if the update models a side-effect of a procedure call that
     can't be turned into C code.  *)
    VAR
      loc: D.Location;
    BEGIN
      IF (res. instr. opcode # Opc.call) THEN
        RETURN FALSE
      ELSE
        loc := res. location;
        IF (loc = NIL) THEN
          (* having NIL for the location of a call instruction means that a
             variable parameter is modified by this value; otherwise it doesn't
             come from a fixed variable and therefore cannot be a side-effect*)
          RETURN (res. instr # res)
        ELSIF (instr. opcode # Opc.updateNonlocal) &
              (instr. opcode # Opc.updateVarParam) THEN
          (* the updated value doesn't come from a Oberon-2 variable, so it
             cannot be the registration of a side-effect *)
          RETURN FALSE
        ELSE
          (* we got an instruction modeling side-effect if the source and the
             destination location are the same *)
          RETURN (instr. opndList. arg = loc(D.SymLocation). var)
        END
      END
    END SideEffect;

  BEGIN
    IF (instr. opcode = Opc.updateMem) THEN
      inOpnd := instr. opndList. nextOpnd
    ELSE
      inOpnd := instr. LastOperand()
    END;
    RETURN Sym.TypeInGroup (inOpnd. OpndType(), D.grpStructured) OR
           (inOpnd. arg IS D.Result) & SideEffect (inOpnd. arg(D.Result)) OR
           (inOpnd. arg IS D.Object)
  END NoopUpdate;

PROCEDURE NoopAccess* (instr: D.Instruction): BOOLEAN;
(* Returns TRUE iff the given access `instr' merely serves as base for another
   access, or to provide the value of a variable to a procedure call that is
   in fact passed per reference (i.e. the value is actually forced into memory
   and the procedure gets it from there).  Such instructions don't read 
   anything from memory themselves and don't have to be translated into target
   code, they are "no operation" instructions.
   pre: instr. opcode DIV sizeClass = Opc.classAccess *)
  VAR
    use: D.Opnd;
    sideEffect: BOOLEAN;
    param: D.Object;
  
  PROCEDURE SameAddress (opnd: D.Opnd; accessAdr: D.Usable): BOOLEAN;
    VAR
      obj: D.Object;
      enter: D.Instruction;
    BEGIN
      obj := opnd. location(D.SymLocation). var(D.Object);
      IF (accessAdr IS D.Result) & 
         (accessAdr(D.Result). instr. opcode = Opc.enter) THEN
        enter := instr. region. EnterInstr();
        RETURN (enter. GetResult (obj, D.symLocAddress) = accessAdr)
      ELSE
        RETURN (accessAdr IS D.Instruction) &
               (accessAdr(D.Instruction). opcode = Opc.adr) &
               (accessAdr(D.Instruction). opndList. arg = obj)
      END
    END SameAddress;
  
  BEGIN
    sideEffect := TRUE;
    use := instr. useList;
    WHILE sideEffect & (use # NIL) DO
      IF (use. instr. opcode = Opc.call) THEN
        param := use. GetFormalParam();
        IF (param # NIL) & (param. mode = D.objVar) OR
           (use. OperandIndex() < 3) OR
           ~SameAddress (use, instr. opndList. nextOpnd. arg) THEN
          sideEffect := FALSE
        END
      ELSIF (use. instr. opcode = Opc.exit) THEN
        IF (use. location # NIL) &
           (use. location(D.SymLocation). var IS D.Object) &
           (use. location(D.SymLocation). var(D.Object). name^="$result") THEN
          (* an operation that delivers a value to an "exit" instruction can be
             ignored unless it corresponds to the "$result" operand, i.e. the
             functions return value *)
          sideEffect := FALSE
        END
      ELSIF ((use. instr. opcode # Opc.accessField) &
             (use. instr. opcode # Opc.accessElement)) OR
            (use. instr. opndList # use) THEN
        sideEffect := FALSE
      END;
      use := use. nextUse
    END;
    RETURN sideEffect
  END NoopAccess;
  
PROCEDURE UpdateSourceAdr* (instr: D.Instruction): D.Opnd;
(* Given a structure update instruction `instr', this function returns the
   address of the variable that provides the source value, or the string
   constant that is used as input.
   pre: (instr. opcode DIV sizeClass = Opc.classUpdate) &
        TypeInGroup (instr. type, D.grpStructured) *)
  VAR
    arg: D.Usable;
    inUpd: D.Instruction;
    inOpnd: D.Opnd;
  BEGIN
    inOpnd := instr. LastOperand();
    arg := inOpnd. arg;
    IF (arg IS D.Const) THEN
      RETURN inOpnd
    ELSIF ElementUpdate (arg) THEN
      (* input is another update; decide if this update did the work for us, 
         i.e. if it modifies a value inside the variable that is updated by
         `instr' *)
      inUpd := inOpnd. arg(D.Instruction);
      (* maybe we have a sequence of consecutive element updates on the same
         structurued value: get the very first of these updates *)
      LOOP
        arg := inUpd. opndList. arg;
        IF ElementUpdate (arg) THEN
          inUpd := arg(D.Instruction)
        ELSE
          EXIT
        END
      END
    END;
    (* here holds: `arg' is either an access or an update instruction (but not
       access-mem or update-mem), or a string copy *)
    ASSERT (arg IS D.Instruction);
    IF (arg(D.Instruction). opcode = Opc.stringCopy) OR
       (arg(D.Instruction). opcode = Opc.structCopy) THEN
      RETURN arg(D.Instruction). NthOperand (4)
    ELSE
      ASSERT ((arg(D.Instruction). opcode DIV Opc.sizeClass = Opc.classUpdate) OR
              (arg(D.Instruction). opcode DIV Opc.sizeClass = Opc.classAccess));
      RETURN arg(D.Instruction). NthOperand (1)
    END
  END UpdateSourceAdr;


PROCEDURE RegClass* (type: D.Struct): SHORTINT;
(* Maps an Oberon-2 type onto one of the register files.  *)
  BEGIN
    CASE type. form OF
    | D.strBoolean..D.strLongInt, D.strSet8..D.strSet32, D.strByte:
      RETURN instrInt
    | D.strPtr, D.strNil, D.strPointer, D.strProc:
      (* `int' for 32 bit, `huge' for 64 bit architecture *)
      IF (D.strAddress = D.strLongInt) THEN
        RETURN instrInt
      ELSE
        RETURN instrHuge
      END
    | D.strHugeInt, D.strSet64:
      RETURN instrHuge
    | D.strReal: 
      RETURN instrReal
    | D.strLongReal: 
      RETURN instrLongReal
    | D.strUndef, D.strStringConst8, D.strStringConst16, D.strNone, 
      D.strArray, D.strOpenArray, D.strRecord:
      RETURN instrVoid  (* these types are handled as part of statments *)
    END
  END RegClass;

PROCEDURE TestInstr* (instr: D.Instruction): BOOLEAN;
  VAR
    opc: INTEGER;
  BEGIN
    opc := instr. opcode;
    RETURN (opc = Opc.boundIndex) OR (opc = Opc.boundRange) OR
           (opc = Opc.typeGuard) OR (opc = Opc.typeAssert)
  END TestInstr;

PROCEDURE Region* (region: D.Region);
(* Classifies every instruction in `region' (and all regions nested in it) with
   respect to the following criterias:
    - does it contribute to the generated C code?
    - into which register file does it store its result?
*)
  VAR
    instr: D.Instruction;
    cat: LONGINT;
    opc, class, subclass: INTEGER;
    from, to: D.Struct;
    use, nextUse: D.Opnd;
    discard: BOOLEAN;
    obj: D.Object;
    greg: D.GlobalRegion;
  
  PROCEDURE TypeCastOp (instr: D.Instruction): BOOLEAN;
    VAR
      from: D.Struct;
    BEGIN
      IF (instr. opcode DIV Opc.sizeClass # Opc.classConv) THEN
        RETURN FALSE
      ELSE
        from := instr. opndList. nextOpnd. OpndType();
        RETURN Sym.TypeInGroup (from, D.grpSet) & 
               (instr. type. form > from. form)
      END
    END TypeCastOp;
  
  BEGIN
    instr := region. instrList;
    WHILE (instr # NIL) DO
      instr. flags := instr. flags - backendFlags;
      
      WITH instr: D.Region DO
        Region (instr)
      ELSE
        opc := instr. opcode;
        class := opc DIV Opc.sizeClass;
        subclass := opc MOD Opc.sizeClass;
        
        IF (instr. type = NIL) THEN
          cat := instrVoid
        ELSE
          cat := RegClass (instr. type)
        END;
        
        IF TestInstr (instr) THEN
          (* runtime check; in GSA form this is formally an expression with an
             result (at least sometimes), in C this is only a statement  *)
          cat := instrVoid
          
        ELSIF (class = Opc.classConv) THEN
          from := instr. opndList. nextOpnd. OpndType();
          to := instr. type;
          IF TypeCastOp (instr) THEN
            (* extending set type (clear upper bits in register) *)
          ELSIF (RegClass (to) = RegClass (from)) THEN
            (* conversions inside the same register file are suppressed unless
               the using instruction is a type cast or an update-mem; in the 
               latter case the type of the source expression cannot be 
               discarded *)
            discard := TRUE;
            use := instr. useList;
            WHILE (use # NIL) DO
              nextUse := use. nextUse;
              IF (use. instr. opcode = Opc.typeCast) OR
                 TypeCastOp (use. instr) OR
                 (use. instr. opcode = Opc.updateMem) THEN
                discard := FALSE
              ELSE
                use. ReplaceOperand (instr. opndList. nextOpnd. arg)
              END;
              use := nextUse
            END;
            IF discard THEN
              cat := instrNoOutput
            END
          END
          
        ELSIF (class < Opc.classAccess) THEN
          CASE opc OF
          | Opc.createStore, Opc.deleteStore:
            cat := instrNoOutput
          | Opc.typeCast:
            IF Sym.TypeInGroup (instr. type, D.grpStructured) THEN
              (* type casts to structured values are folded into struct-copy
                 instructions *)
              cat := instrNoOutput
            END
          | Opc.typeTag:
            cat := RegClass (D.struct[D.strAddress])
          | Opc.copy:
            IF (cat = instrVoid) THEN
              (* copy intructions of structured type are introduced by the 
                 special handling of large constant arrays by oo2c (see
                 CodeGen.CollectInitialization); such instructions do not
                 produce any code and should be ignored; copies of scalar
                 type are introduced by Allocate.ResolveVarConflicts and are
                 used to move variables into "registers" *)
              cat := instrNoOutput
            END
          | Opc.gate:
            (* code for gates is always placed outside the merge *)
            INCL (instr. flags, instrNoOutput)
          ELSE  (* use category of result type *)
          END
          
        ELSE
          CASE class OF
          | Opc.classAccess:
            IF (cat = instrVoid) OR NoopAccess (instr) THEN
              (* structured result: access will be combined with the
                 corresponding update instruction into a copy statement, or it
                 merely reflects a side-effect of a called procedure *)
              cat := instrNoOutput
            END
            
          | Opc.classUpdate:
            INCL (instr. flags, instrVoid);  (* always statement *)
            IF NoopUpdate (instr) THEN
              (* cascaded update, this instruction doesn't change anything in
                 memory *)
              cat := instrNoOutput
            ELSE
              cat := instrVoid
            END
          ELSE  (* use category of result type *)
          END
        END;
        INCL (instr. flags, cat);
        
        IF (instr. opcode = Opc.call) &
           (instr. opndList. nextOpnd. nextOpnd. arg IS D.Object) THEN
          (* call with constant target *)
          obj := instr. opndList. nextOpnd. nextOpnd. arg(D.Object);
          IF (D.objIsSpecialCodeProc IN obj. flags) &
             (obj. data(D.Const). int = spPushContext) THEN
            (* we got a call to Exceptions.PUSHCONTEXT; mark greg so that 
               additional declarations are inserted for the PUSHCONTEXT code *)
            greg := instr. Greg();
            INCL (greg. flags, instrSpecialDecl)
          END
        END
      END;
      
      instr := instr. nextInstr
    END
  END Region;

END Classify.
