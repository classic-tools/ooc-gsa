(*	$Id: AliasAnalysis.Mod,v 1.20 1999/03/15 18:55:09 acken Exp $	*)
MODULE AliasAnalysis;
(*  Inspects aliasing relationships between intructions.
    Copyright (C) 1995-1999  Michael van Acken

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
  D := Data, Opc := Opcode, Sym := SymbolTable, Worklist;

(* ... missing:
improvements on update instructions
code to detect unnecessary local copies of structured value parameters
  only does static checks, does not permit run-time checks yet
*)

CONST
  noAlias* = -1;
  mayAlias* = 0;
  doAlias* = 1;

CONST
  accessOrUpdate* = 0;
  onlyAccess* = 1;
  onlyUpdate* = 2;

VAR
  enabled*: BOOLEAN;
  (* first call to `Analyse' sets it to TRUE; for debugging purposes *)

VAR
  worklist: Worklist.Worklist;


PROCEDURE ArrayCompatible (a, b: D.Struct): BOOLEAN;
(* Returns TRUE iff `a' is array compatible to `b'.  *)
  BEGIN
    WHILE (a. form = D.strOpenArray) &
          Sym.TypeInGroup (b, D.grpArray) DO
      a := a. base; b := b. base
    END;
    RETURN Sym.SameType (a, b)
  END ArrayCompatible;

PROCEDURE SubtypeOf (subStruct, superStruct: D.Struct;
                     arrayCompat: BOOLEAN): BOOLEAN;
(* Returns TRUE iff type `superStruct' is equal to or contains a subtype of
   type `subStruct'.  If `arrayCompat' is TRUE also returns TRUE if a subtype
   of `superStruct' is array compatible to `subStruct'.  *)
  VAR 
    field: D.Object;
  BEGIN
    IF Sym.EqualTypes (superStruct, subStruct) OR 
       Sym.ExtensionOf (superStruct, subStruct) THEN
      RETURN TRUE
    ELSIF arrayCompat & ArrayCompatible (subStruct, superStruct) THEN
      RETURN TRUE
    ELSIF Sym.TypeInGroup (superStruct, D.grpArray) THEN
      RETURN SubtypeOf (subStruct, superStruct. base, arrayCompat)
    ELSIF (superStruct. form = D.strRecord) THEN
      (* inspect types of all fields of all base types *)
      WHILE (superStruct # NIL) DO
        field := superStruct. decl;
        WHILE (field # NIL) DO
          IF (field. mode = D.objField) & 
             SubtypeOf (subStruct, field. type, arrayCompat) THEN
            RETURN TRUE
          END;
          field := field. rightObj
        END;
        superStruct := superStruct. base
      END;
      RETURN FALSE
    ELSE
      RETURN FALSE
    END
  END SubtypeOf;

PROCEDURE Aliasing* (i0: D.Instruction; m0: SHORTINT;
                     i1: D.Instruction; m1: SHORTINT): SHORTINT;
(* Determines whether the two instructions `i0' and `i1' effect (reading or
   writing) the same memory area.  If the areas are identic, `doAlias' is
   returned, if they overlap or might overlap it will be `mayAlias', otherwise
   the function's result is `noAlias'.  
   
   The mode selectors `m0' and `m1' take one of the values `onlyAccess', 
   `onlyUpdate', or `accessOrUpdate'.  For string-copy and struct-copy they 
   determine whether just the access designator, just the update designator, or
   both should be considered.  For all other instructions they have no effect.
   
   Actually this predicate doesn't do a full analysis of memory access patterns
   in the GSA code.  For simplicity all instructions are divided into three
   partitions: variables (nonlocal, heap objects, and variable parameters),
   records, and arrays.  If two instructions come from different partitions,
   it is assumed that no aliasing can occur.  The using procedure of this 
   predicate has to deal with these eventualities.  *)
  CONST
    noAliasOp = -1;
    maxSelect = 16;
    catMemory = 0;
    catCall = 1;
    catVarParam = 2;
    catHeap = 3;
    catNonlocal = 4;
    catLocal = 5;
    catField = 6;
    catElement = 7;
  TYPE
    Selector = RECORD
      category: SHORTINT;
      var: D.Usable;
      type: D.Struct;
      instr: D.Instruction;
    END;
    Designator = ARRAY maxSelect OF Selector;
  VAR
    l0, l1: INTEGER;
    d0, d1: Designator;
    res: SHORTINT;

  PROCEDURE HandleGate (gate: D.Gate; gateMode: SHORTINT;
                        i: D.Instruction; iMode: SHORTINT): SHORTINT;
    VAR
      class, subcl: INTEGER;
      ref: D.Instruction;  (* debug *)
      
    PROCEDURE CheckStoreGate (baseInstr: D.Instruction; baseMode: SHORTINT;
                              gate: D.Instruction; gateMode: SHORTINT;
                              outerRegion: D.Region): SHORTINT;
    (* Determines the aliasing relationship between `baseInstr' and `gate'.  If
       all paths through the gate originating in `outerRegion' do not alias 
       with `baseInstr', the whole gate won't alias.  
       pre: `gate' designates a $store value *)
      VAR
        opnd, opnd0: D.Opnd;
        alias: SHORTINT;
        value: D.Instruction;
      BEGIN
        IF (gate. opndList. arg(D.Merge). opcode = Opc.mergeLoop) &
           (gate. opcode > noAliasOp) THEN
          (* a loop gate aliases with `baseInstr' if one of its arguments 
             aliases with it; problem: we have to make sure that the algorithm
             terminates for the backedge operand, so we turn `gate' into a 
             instruction that won't alias with anything *)
          gate. opcode := -Opc.gate;
          alias := CheckStoreGate (baseInstr, baseMode, gate, gateMode, outerRegion);
          gate. opcode := Opc.gate;
          RETURN alias
        ELSE
          (* normal gate; only if none of the arguments alias with the
             reference instruction, a `noAlias' is returned *)
          opnd := gate. opndList. nextOpnd;
          WHILE (opnd # NIL) DO
            value := opnd. arg(D.Result). instr;
            WHILE (value # NIL) & ~value. region. Dominates (outerRegion) DO
              IF (value. opcode = Opc.gate) THEN
                alias := CheckStoreGate (baseInstr, baseMode, 
                                         value, gateMode, outerRegion)
              ELSE
                alias := Aliasing (baseInstr, baseMode, value, gateMode)
              END;
              IF (alias # noAlias) THEN
                RETURN mayAlias
              ELSIF (value. opcode = Opc.gate) OR
                    (value. opcode <= noAliasOp) THEN
                value := NIL
              ELSE
                CASE value. opcode OF
                | Opc.updateNonlocal, Opc.updateVarParam, Opc.updateHeap:
                  opnd0 := value. NthOperand (2)
                | Opc.call:
                  opnd0 := value. GetOperand (Sym.store, D.symLocObject)
                END;
                value := opnd0. arg(D.Result). instr
              END
            END;
            IF (value # NIL) THEN  (* debug *)
              IF (ref # NIL) THEN
                ASSERT (ref = value)
              ELSE
                ref := value
              END
            END;
            opnd := opnd. nextOpnd
          END;
          RETURN noAlias
        END
      END CheckStoreGate;

    BEGIN
      class := i. opcode DIV Opc.sizeClass;
      subcl := i. opcode MOD Opc.sizeClass;
      IF (gate. var = Sym.store) &
         ((class = Opc.classAccess) OR (class = Opc.classUpdate)) &
         ((subcl = Opc.subclHeap) OR (subcl = Opc.subclNonlocal) OR
          (subcl = Opc.subclVarParam)) THEN
        ref := NIL;
        IF (gate. opndList. arg(D.Merge). opcode = Opc.mergeLoop) THEN
          RETURN CheckStoreGate (i, iMode, gate, gateMode, gate. region. region)
        ELSE
          RETURN CheckStoreGate (i, iMode, gate, gateMode, i. region)
        END
      ELSIF (i. opcode = Opc.gate) THEN
        IF (gate. var = i(D.Gate). var) THEN
          RETURN doAlias
        ELSE
          RETURN noAlias
        END
      ELSE 
        RETURN mayAlias
      END
    END HandleGate;
  
  PROCEDURE GetsVarAddress (call: D.Instruction; var: D.Object): BOOLEAN;
  (* Returns TRUE if the address of `var' is directly fed into `call'.
     pre: `var' is a nonlocal variable *)
    VAR
      adr: D.Result;
      opnd: D.Opnd;
      proc: D.Usable;
      enter: D.Instruction;
    
    PROCEDURE VarParAddress (res: D.Result): BOOLEAN;
    (* Check `res' if is the address of a variable parameter with the same type
       as `var'.  In this case the nonlocal variable `var' might be identical
       to the variable parameter, allowing the called procedure to modify
       its value through the parameter.  *)
      VAR
        loc: D.SymLocation;
        obj: D.Object;
      BEGIN
        IF (res. instr. opcode = Opc.enter) THEN
          loc := res. location(D.SymLocation);
          IF (loc. var IS D.Object) & (loc. attrib = D.symLocAddress) THEN
            obj := loc. var(D.Object);
            RETURN (obj. mode = D.objVarPar) &
                   (obj. level >= var. level) & (obj. type = var. type)
          ELSE
            RETURN FALSE
          END
        ELSE
          RETURN FALSE
        END
      END VarParAddress;
    
    BEGIN
      (* if the called procedure is declared in the same scope is the 
         variable, or in a scope nested more deeply, it's assumed it can 
         "see" the variable if it reads from $mem; if the called procedure
         is global, assume it can always access global variables *)
      proc := call. NthArgument (2);
      IF (proc IS D.Object) & (proc(D.Object). level >= var. level) &
         (call. GetResult (Sym.mem, D.symLocObject) # NIL) THEN
        RETURN TRUE
      ELSIF ~(proc IS D.Object) & (var. level = 0) THEN
        RETURN TRUE
      END;
      
      (* check if the address of `var' (it is represented by a result of
         enter) appears as argument of `call', or if an argument of `call'
         is a variable parameter of the caller with the same type as
         `var'  *)
      enter := call. region. EnterInstr();
      adr := enter. GetResult (var, D.symLocAddress);
      opnd := call. opndList;
      WHILE (opnd # NIL) DO
        IF (opnd. arg = adr) OR 
           (opnd. arg IS D.Result) & VarParAddress (opnd. arg(D.Result)) THEN
          RETURN TRUE
        END;
        opnd := opnd. nextOpnd
      END;
      
      (* finally check whether the variable appears as part of the call's list
         of side-effects *)
      RETURN (call. GetResult (var, D.symLocObject) # NIL)
    END GetsVarAddress;
  
  PROCEDURE CopyAlias (copy: D.Instruction; copyMode: SHORTINT;
                       instr: D.Instruction; instrMode: SHORTINT): SHORTINT;
  (* A copy instruction (struct-copy or string-copy) affects two memory
     locations: source and destination.  An instruction doesn't alias with
     a copy if it doesn't alias with source or destination.  *)
    VAR
      arg: D.Usable;
      opcode: INTEGER;
      res0, res1: SHORTINT;
    BEGIN
      opcode := copy. opcode;
      copy. opcode := -opcode;
      IF (copyMode # onlyAccess) THEN
        arg := copy. NthArgument (1);
        IF (arg IS D.Result) & (arg(D.Result). instr. opcode = Opc.adr) THEN
          (* destination is a local variable of the procedure; use the address
             instruction as a placeholder for the variable *)
          res0 := Aliasing (arg(D.Result). instr, copyMode, instr, instrMode)
        ELSE
          res0 := Aliasing (copy. opndList. arg(D.Result). instr, copyMode, 
                            instr, instrMode)
        END
      ELSE  (* mode selector doesn't include update part *)
        res0 := noAlias
      END;
      
      IF (res0 # mayAlias) THEN
        IF (copyMode # onlyUpdate) THEN
          arg := copy. NthArgument (4);
          IF (arg IS D.Result) & (arg(D.Result). instr. opcode = Opc.adr) THEN
            (* source is a local variable of the procedure; use the address
             instruction as a placeholder for the variable *)
            res1 := Aliasing (arg(D.Result). instr, copyMode, instr, instrMode)
          ELSE
            arg := copy. NthArgument (3);
            res1 := Aliasing (arg(D.Result). instr, copyMode, instr, instrMode)
          END
        ELSE  (* mode selector doesn't include update part *)
          res1 := noAlias
        END;
        
        IF (res0 # noAlias) OR (res1 # noAlias) THEN
          res0 := mayAlias
        END
      END;
      copy. opcode := opcode;
      RETURN res0
    END CopyAlias;
  
  PROCEDURE WildOpcode (opc: INTEGER): BOOLEAN;
  (* Returns TRUE iff `opc' can alias with anything.  *)
    BEGIN
      RETURN (opc = Opc.accessMem) OR (opc = Opc.updateMem) OR 
             (opc = Opc.bit) OR (opc = Opc.move) OR
             (opc = Opc.enter) OR (opc = Opc.createStore)
    END WildOpcode;
  
  PROCEDURE BuildDesignator (i: D.Instruction; 
                             VAR d: Designator; VAR level: INTEGER);
  (* Reconstructs an Oberon-2 designator from instruction `i', placing the
     result in the array `d', starting at index `level'.  When finished 
     `d[level]' will hold the topmost variable (variable parameter, heap 
     object), and `d[level-1]', `d[level-2]', ..`d[0]' the selectors applied 
     to this variable.  *)
    VAR
      rvalue: D.Usable;
      
    PROCEDURE SetSelector (i: D.Instruction; VAR s: Selector);
      VAR
        res: D.Result;
        opnd0: D.Opnd;
        
      PROCEDURE GetLocalAdr (u: D.Usable): D.Instruction;
      (* Retrieves the "adr x" instruction from the expression `u'.  *)
        VAR
          i, j: D.Instruction;
        BEGIN
          IF (u IS D.Instruction) THEN
            i := u(D.Instruction);
            IF (i. opcode = Opc.adr) THEN
              RETURN i
            ELSIF (i. opcode = Opc.gate) THEN
              RETURN GetLocalAdr (i. opndList. nextOpnd. arg)
            ELSIF (Opc.baseAdd <= i. opcode) & 
                  (i. opcode < Opc.baseSub+Opc.sizeClass) THEN
              j := GetLocalAdr (i. opndList. arg);
              IF (j = NIL) THEN
                RETURN GetLocalAdr (i. opndList. nextOpnd. arg)
              ELSE
                RETURN j
              END
            ELSE
              RETURN NIL
            END
          ELSE
            RETURN NIL
          END
        END GetLocalAdr;
      
      PROCEDURE Base (value, adr: D.Usable): D.Instruction;
        VAR
          class: INTEGER;
        BEGIN
          IF (value IS D.Instruction) THEN
            class := value(D.Instruction). opcode DIV Opc.sizeClass;
            IF (class = Opc.classAccess) OR (class = Opc.classUpdate) THEN
              RETURN value(D.Instruction)
            ELSIF  (value(D.Instruction). opcode = Opc.typeGuard) THEN
              RETURN Base (value(D.Instruction). opndList. arg, adr)
            END
          END;
          RETURN GetLocalAdr (adr)
        END Base;
      
      PROCEDURE FollowUpdate (i: D.Instruction);
        VAR
          use: D.Opnd;
        BEGIN
          (* get the next higher update instruction *)
          use := i. useList;
          WHILE (use # NIL) DO
            IF (use. instr. opcode DIV Opc.sizeClass = Opc.classUpdate) &
               (use. instr. NthOperand (3) = use) THEN
              BuildDesignator (use. instr, d, level);
              RETURN
            END;
            use := use. nextUse
          END;
          (* couldn't find any update, meaning we modified a local variable *)
          d[level]. instr := GetLocalAdr (i. opndList. nextOpnd. arg);
          d[level]. category := catLocal;
          d[level]. var := d[level]. instr. opndList. arg;
          d[level]. type := d[level]. var(D.Object). type
        END FollowUpdate;
      
      BEGIN
        s. instr := i;
        CASE i. opcode OF
        | Opc.call:
          s. category := catCall;
          s. var := NIL;
          s. type := NIL
        | Opc.adr:
          s. category := catLocal;
          s. var := i. opndList. arg;
          s. type := i. opndList. OpndType()
        | Opc.zero:
          s. category := catLocal;
          s. var := i. opndList. arg;
          s. type := i. opndList. OpndType()
        | Opc.gate:
ASSERT ((i(D.Gate).var.name[0] # "$"));
          s. category := catLocal;
          s. var := i(D.Gate). var;
          s. type := s. var(D.Object). type
        | Opc.typeAssert, Opc.typeGuard:
          SetSelector (i. opndList. arg(D.Instruction), s)
        | Opc.accessHeap, Opc.updateHeap:
          s. category := catHeap;
          s. var := i. opndList. arg;
          s. type := s. var(D.Struct)
        | Opc.accessNonlocal, Opc.updateNonlocal:
          s. category := catNonlocal;
          s. var := i. opndList. arg;
          s. type := s. var(D.Object). type
        | Opc.accessVarParam, Opc.updateVarParam:
          s. category := catVarParam;
          s. var := i. opndList. arg;
          s. type := s. var(D.Object). type
        
        | Opc.accessField, Opc.accessElement:
          IF (i. opcode = Opc.accessField) THEN
            s. category := catField
          ELSE
            s. category := catElement
          END;
          s. var := i. opndList. nextOpnd. nextOpnd. arg;
          s. type := i. type;
          INC (level);
          rvalue := i. opndList. arg;
          IF (rvalue IS D.Result) &
             (rvalue(D.Result). instr. opcode = Opc.enter) THEN
            res := rvalue(D.Result);
            d[level]. instr := res. instr;
            d[level]. category := catLocal;
            d[level]. var := res. location(D.SymLocation). var(D.Object);
            d[level]. type := d[level]. var(D.Object). type
          ELSIF (rvalue IS D.Instruction) &
                ((ABS (rvalue(D.Instruction). opcode) = Opc.structCopy) OR
                 (ABS (rvalue(D.Instruction). opcode) = Opc.stringCopy)) THEN
            d[level]. instr := GetLocalAdr (i. opndList. nextOpnd. arg);
            d[level]. category := catLocal;
            d[level]. var := d[level]. instr. opndList. arg(D.Object);
            d[level]. type := d[level]. var(D.Object). type
          ELSIF (rvalue IS D.Instruction) &
                (rvalue(D.Instruction). opcode DIV Opc.sizeClass = 
                                                          Opc.classUpdate) THEN
            FollowUpdate (rvalue(D.Instruction))
          ELSE
            BuildDesignator (Base (rvalue, i. opndList. nextOpnd. arg),
                             d, level)
          END
        | Opc.updateField, Opc.updateElement:
          IF (i. opcode = Opc.updateField) THEN
            s. category := catField
          ELSE
            s. category := catElement
          END;
          s. var := i. opndList. nextOpnd. nextOpnd. arg;
          opnd0 := i. NthOperand (3);
          s. type := opnd0. OpndType();
          INC (level);
          FollowUpdate (i)
        
        | Opc.accessMem, Opc.updateMem:
          s. category := catMemory
        END
      END SetSelector;
    
    BEGIN
      SetSelector (i, d[level])
    END BuildDesignator;
  
(*debug  PROCEDURE WriteDesignator (VAR d: Designator; l: INTEGER);
    VAR
      l0: INTEGER;
    BEGIN
      l0 := l;
      WHILE (l >= 0) DO
        CASE d[l]. category OF
        | catCall:
          Out.String ("call")
        | catVarParam:
          Out.String ("var-param: ");
          Out.String (d[l]. var(D.Object). name^)
        | catHeap:
          Out.String ("heap: <struct>");
          IF (d[l]. var(D.Struct). obj # NIL) THEN
          Out.String (d[l]. var(D.Struct). obj. name^)
          END
        | catNonlocal:
          Out.String ("nonlocal: ");
          Out.String (d[l]. var(D.Object). name^)
        | catLocal:
          Out.String ("local: ");
          IF (d[l]. var IS D.Const) THEN
            Out.String ("<string const>")
          ELSE
            Out.String (d[l]. var(D.Object). name^)
          END
        | catField:
          Out.String (".");
          Out.String (d[l]. var(D.Object). name^)
        | catElement:
          Out.String ("[]");
        END;
        DEC (l)
      END;
      Out.String ("  (");
      Out.Int (l0, 0);
      Out.String (")   ");
      Out.Ln
    END WriteDesignator;*)
  
  PROCEDURE ComputeAliasing (VAR d0: Designator; l0: INTEGER; 
                             VAR d1: Designator; l1: INTEGER): SHORTINT;
    (* pre: d0[l0]. category < d1[l1]. category *)
    VAR
      alias: SHORTINT;
      f0, f1: D.Object;
      
    PROCEDURE ArrayOfByte (i: D.Instruction): BOOLEAN;
      VAR
        obj: D.Object;
      BEGIN
        obj := i. opndList. arg(D.Object);
        RETURN (obj. mode = D.objVarPar) &
               (obj. type. form = D.strOpenArray) &
               (obj. type. base. form = D.strByte)
      END ArrayOfByte;

    BEGIN
      alias := mayAlias;
      CASE d0[l0]. category OF
      | catMemory:
        RETURN mayAlias  (* assume the worst for direct memory manipulation *)
      | catCall:
        IF (d1[l1]. category = catNonlocal) THEN
          (* do some fine tuning for accesses to nonlocal variables across
             procedure calls; if the called procedure isn't passed the
             address of the variable directly, assume that it isn't
             changed by the call; note that this simple check will not
             for structured values *)
          IF ~Sym.TypeInGroup (d1[l1]. type, D.grpStructured) &
             ~GetsVarAddress (d0[l0]. instr, d1[l1]. var(D.Object)) THEN
            RETURN noAlias
          END
        END;
        (* note: with a more sophisticated test the predicate 
           `TransitiveStoreAlias' below has to be adjusted, too *)
        RETURN mayAlias
      | catVarParam:
        IF (d1[l1]. category = catVarParam) & (d0[l0]. var = d1[l1]. var) THEN
          alias := doAlias
        ELSIF (d1[l1]. category = catLocal) THEN
          RETURN noAlias
        ELSIF ArrayOfByte (d0[l0]. instr) OR
              (d1[l1].category = catVarParam) & ArrayOfByte (d1[l1].instr) THEN
          RETURN mayAlias
        ELSIF SubtypeOf (d0[l0]. type, d1[l1]. type, TRUE) OR 
              SubtypeOf (d1[l1]. type, d0[l0]. type, 
                         d1[l1]. category = catVarParam) THEN
          IF (d1[l1]. category = catVarParam) THEN
            (* both designators belong to variable parameters; continuing the
               analysis on them is tricky, so we stick with `mayAlias' *)
            RETURN mayAlias
          ELSE
            alias := mayAlias
          END
        ELSE
          RETURN noAlias
        END
      | catHeap:
        IF (d1[l1]. category = catHeap) THEN
          IF (d0[l0]. instr. opndList. nextOpnd. arg = 
              d1[l1]. instr. opndList. nextOpnd. arg) &
             (d0[l0]. type = d1[l1]. type) THEN
            (* both addresses match, and the accessed types are identical *)
            alias := doAlias
          ELSIF (d0[l0]. type = d1[l1]. type) OR
                Sym.ExtensionOf (d0[l0]. type, d1[l1]. type) OR
                Sym.ExtensionOf (d1[l1]. type, d0[l0]. type) THEN
            alias := mayAlias
          ELSE
            RETURN noAlias
          END
        ELSE
          RETURN noAlias
        END
      | catNonlocal, catLocal:
        IF (d0[l0]. category = d1[l1]. category) & 
           (d0[l0]. var = d1[l1]. var) THEN
          alias := doAlias
        ELSE
          RETURN noAlias
        END
      END;
      
      (* only one of the designators is based upon a variable parameter; move
         strip the prefix from the other designator until both the variable 
         parameter and the other designator are compatible *)
      IF (d0[l0]. category = catVarParam) THEN
        WHILE (l1 >= 0) &
              ~(Sym.EqualTypes (d0[l0]. type, d1[l1]. type) OR
                ArrayCompatible (d0[l0]. type, d1[l1]. type)) DO
          DEC (l1)
        END
      ELSIF (d1[l1]. category = catVarParam) THEN
        WHILE (l0 >= 0) &
              ~(Sym.EqualTypes (d1[l1]. type, d0[l0]. type) OR
                ArrayCompatible (d1[l1]. type, d0[l0]. type)) DO
          DEC (l0)
        END
      END;
      DEC (l0); DEC (l1);
      
      WHILE (l0 >= 0) & (l1 >= 0) DO
        ASSERT (d0[l0]. category = d1[l1]. category);
        CASE d0[l0]. category OF
        | catField:
          f0 := d0[l0]. var(D.Object);
          f1 := d1[l1]. var(D.Object);
          IF (f0. offset >= f1. offset + f1. type. size) OR
             (f0. offset + f0. type. size <= f1. offset) THEN
            (* the memory intervalls don't intersect; this test works for
               record and union types *)
            RETURN noAlias
          ELSIF (alias = doAlias) & (f0 # f1) THEN
            alias := mayAlias
          END
        | catElement:
          IF (alias = doAlias) & (d0[l0]. var # d1[l1]. var) THEN
            alias := mayAlias
          ELSIF (d0[l0]. var IS D.Const) & (d1[l1]. var IS D.Const) &
                (d0[l0]. var(D.Const). int # d1[l1]. var(D.Const). int) THEN
            (* the indices are constants of different values *)
            RETURN noAlias
          END
        ELSE
          alias := mayAlias
        END;
        DEC (l0); DEC (l1)
      END;
      IF (l0 # l1) THEN
        RETURN mayAlias
      ELSE
        RETURN alias
      END
    END ComputeAliasing;
  
  BEGIN
    IF (i0 = i1) THEN
      RETURN doAlias
      
    ELSIF WildOpcode (i0. opcode) OR WildOpcode (i1. opcode) OR ~enabled THEN
      (* any direkt memory access may alias with any other operation *)
      RETURN mayAlias
    
    ELSIF (i0. opcode <= noAliasOp) OR (i1. opcode <= noAliasOp) THEN
      (* pseudo opcode introduced by `CheckStoreGate'; doesn't alias with 
         anything *)
      RETURN noAlias
        
    (* the copy instructions a somewhat problematic: the alias with two 
       different memory regions, the source and the destination *)
    ELSIF (i0. opcode = Opc.stringCopy) OR (i0. opcode = Opc.structCopy) THEN
      RETURN CopyAlias (i0, m0, i1, m1)
    ELSIF (i1. opcode = Opc.stringCopy) OR (i1. opcode = Opc.structCopy) THEN
      RETURN CopyAlias (i1, m1, i0, m0)
    
    (* there exist two kind of gates: gates bound to local variables of the
       procedure, and gates for $store values; since $store covers a lot of
       room, we go to great lengths to determine whether an access ti $store
       aliases with a particular gate *)
    ELSIF (i0. opcode = Opc.gate) THEN
      RETURN HandleGate (i0(D.Gate), m0, i1, m1)
    ELSIF (i1. opcode = Opc.gate) THEN
      RETURN HandleGate (i1(D.Gate), m1, i0, m0)
    
    ELSE
      l0 := 0; l1 := 0;
      BuildDesignator (i0, d0, l0);
      BuildDesignator (i1, d1, l1);
      IF (d0[l0]. category < d1[l1]. category) THEN
        res := ComputeAliasing (d0, l0, d1, l1)
      ELSE
        res := ComputeAliasing (d1, l1, d0, l0)
      END;
      RETURN res
    END
  END Aliasing;

PROCEDURE TransitiveStoreAlias* (a, b: D.Instruction): BOOLEAN;
(* Returns TRUE if all instructions further up the $store chain from `b' will
   alias with `b' if they alias with `a'.  In other words: If `a' depends on
   `b', it'll depend on all instructions (and their accesses) further up the 
   $store chain without special precautions.  This is used by the scheduler to
   reduce execution time of the anti-dependence algorithm.  
   Note that _without_ running an alias analysis the answer can always be TRUE,
   and that FALSE is always a correct answer.  
   pre: a is an updating instruction *)
  BEGIN
    RETURN ~enabled OR 
           ((b. opcode = Opc.call) & 
            (Aliasing (a, onlyUpdate, b, accessOrUpdate) # noAlias))
  END TransitiveStoreAlias;


PROCEDURE IsAccess (dummy: D.Result; instr: D.Instruction): BOOLEAN;
  VAR
    opc: INTEGER;
  BEGIN
    opc := instr. opcode;
    RETURN (Opc.accessField <= opc) & (opc <= Opc.accessVarParam)
  END IsAccess;

PROCEDURE SimplifyAccess (instr: D.Instruction);
(* Inspect every access instruction and change its $store argument to the most
   recent update instruction that might alias with the access.  This "pushing
   back" of the reference argument in the chain of $store values increases the
   chance to find common subexpressions, allowing to keep more nonlocal 
   references in registers.  If an access can be reduced to a matching update,
   it will be replaced by the updated value.  *)
  VAR
    store: D.Result;
    opnd, newOpnd: D.Opnd;
    alias: SHORTINT;
  
  PROCEDURE AttemptReplacement (instr: D.Instruction; with: D.Opnd);
    VAR
      opcode: INTEGER;
    BEGIN
      IF (with. arg IS D.Result) THEN
        opcode := with. arg(D.Result). instr. opcode;
        IF (opcode DIV Opc.sizeClass # Opc.classUpdate) THEN
          (* never replace an access-instruction with a result from an enter,
             call, struct-copy, or string-copy; the former only serve to model
             side-effects and don't correspond to "real" values, the latter 
             do not participate in the $store chain *)
          RETURN
        END
      END;
      worklist. AddUsingInstr (instr, IsAccess);
      instr. ReplaceUses (with. arg)
    END AttemptReplacement;
  
  PROCEDURE GetGateBase (opnd: D.Opnd; outerRegion: D.Region): D.Opnd;
  (* Get the value of `opnd.arg', a gate designating a $store value, back to 
     get the value originating in `outerRegion'.  Returns an operand that takes
     this value as input.  *)
    VAR
      value: D.Instruction;
    BEGIN
      REPEAT
        value := opnd. arg(D.Result). instr;
        CASE value. opcode OF
        | Opc.gate:
          opnd := value. opndList. nextOpnd
        | Opc.call:
          opnd := value. GetOperand (Sym.store, D.symLocObject)
        | Opc.updateNonlocal, Opc.updateVarParam, Opc.updateHeap:
          opnd := value. NthOperand (2)
        END
      UNTIL opnd. arg(D.Result). instr. region. Dominates (outerRegion);
      RETURN opnd
    END GetGateBase;
  
  BEGIN
    alias := mayAlias;
    CASE instr. opcode OF
    | Opc.accessHeap, Opc.accessNonlocal, Opc.accessVarParam:
      (* check along the $store chain *)
      opnd := instr. LastOperand();
      newOpnd := opnd;
      store := newOpnd. arg(D.Result);
      alias := Aliasing (instr, accessOrUpdate, store. instr, accessOrUpdate);
      WHILE (alias = noAlias) DO
        CASE store. instr. opcode OF
        | Opc.call:
          newOpnd := store. instr. GetOperand (Sym.store, D.symLocObject)
        | Opc.gate:
          IF (store. instr. opndList. arg(D.Merge). opcode = Opc.mergeLoop) THEN
            newOpnd := GetGateBase (newOpnd, store. instr. region. region)
          ELSE
            newOpnd := GetGateBase (newOpnd, instr. region)
          END
        ELSE
          newOpnd := store. instr. NthOperand (store. instr. NumOfOperands()-2)
        END;
        store := newOpnd. arg(D.Result);
        alias := Aliasing (instr, accessOrUpdate, store. instr, accessOrUpdate)
      END;
      IF (alias = doAlias) &
         (instr. NthArgument (2) = store. instr. nextResult) THEN
        (* the access is now coupled to a matching update *)
        AttemptReplacement (instr, store. instr. LastOperand())
      ELSIF (opnd. arg # store) THEN
        opnd. ReplaceOperand (store)
      END

    | Opc.accessField, Opc.accessElement:
      opnd := instr. opndList;
      newOpnd := opnd;
      IF (newOpnd. arg IS D.Result) THEN
        alias := Aliasing (instr, accessOrUpdate, 
                           newOpnd. arg(D.Result). instr, accessOrUpdate)
      END;
      WHILE (newOpnd. arg IS D.Result) & (alias = noAlias) DO
        newOpnd := newOpnd. arg(D.Result). instr. opndList;
        IF (newOpnd. arg IS D.Result) THEN
          alias := Aliasing (instr, accessOrUpdate, 
                             newOpnd. arg(D.Result). instr, accessOrUpdate)
        END
      END;
      IF (newOpnd. arg IS D.Result) & (alias = doAlias) THEN
        (* the access is now coupled to a matching update *)
        AttemptReplacement (instr,
                            newOpnd. arg(D.Result). instr. LastOperand())
      ELSIF (opnd. arg # newOpnd. arg) THEN
        instr. opndList. ReplaceOperand (newOpnd. arg)
      END
    ELSE  (* ignore the rest *)
    END
  END SimplifyAccess;

PROCEDURE Analyse* (greg: D.Region);
  VAR
    info: D.Info;
    
  PROCEDURE AddAccessInstr (r: D.Region);
    VAR
      instr: D.Instruction;
      opc: INTEGER;
    BEGIN
      instr := r. instrList;
      WHILE (instr # NIL) DO
        IF (instr IS D.Region) THEN
          AddAccessInstr (instr(D.Region))
        ELSE
          opc := instr. opcode;
          IF (Opc.accessField <= opc) & (opc <= Opc.accessVarParam) THEN
            worklist. AddHead (instr)
          END
        END;
        instr := instr. nextInstr
      END
    END AddAccessInstr;
  
  BEGIN
    enabled := TRUE;
    greg(D.GlobalRegion). NumberDominanceTree();
    
    AddAccessInstr (greg);
    WHILE ~worklist. IsEmpty() DO
      info := worklist. GetHead();
      worklist. RemoveHead;
      SimplifyAccess (info(D.Instruction))
    END;
    
    (* ... *)
  END Analyse;


PROCEDURE NeedLocalCopy* (greg: D.GlobalRegion; fpar: D.Object): BOOLEAN;
  VAR
    loc: D.SymLocation;
    exit: D.Instruction;
    opnd: D.Opnd;
  BEGIN
    exit := greg. ExitInstr();
    IF (D.objIsUpdated IN fpar. flags) THEN
      RETURN TRUE
    END;
    
    opnd := exit. opndList;
    WHILE (opnd # NIL) DO
      loc := opnd. location(D.SymLocation);
      IF (loc. var = Sym.mem) THEN  (* possibly modifies anything *)
        RETURN TRUE
      ELSIF (loc. var IS D.Struct) THEN  (* modifies heap object *)
        IF SubtypeOf (fpar. type, loc. var(D.Struct), TRUE) THEN
          RETURN TRUE
        END
      ELSIF (loc. var(D.Object). mode = D.objVar) THEN  (* nonlocal var *)
        IF SubtypeOf (fpar. type, loc. var(D.Object). type, TRUE) &
           (loc. var(D.Object). name[0] # "$") THEN
          RETURN TRUE
        END
      ELSE  (* variable parameter *)
        ASSERT (loc. var(D.Object). mode = D.objVarPar);
        IF SubtypeOf (loc. var(D.Object). type, fpar. type, TRUE) OR
           SubtypeOf (fpar. type, loc. var(D.Object). type, TRUE) THEN
          RETURN TRUE
        END
      END;
      opnd := opnd. nextOpnd
    END;
    RETURN FALSE
  END NeedLocalCopy;

BEGIN
  enabled := FALSE
END AliasAnalysis.
