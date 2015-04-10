MODULE ConstPropagation;
(*  Constant folding and optimistic constant propagation.
    Copyright (C) 1995-1998  Juergen Zimmermann

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
  SYSTEM, LowLReal, Termination,
  O := Out, GSA := WriteGSA, Error,
  D := Data, Opc := Opcode, Int := IntArith, Sym := SymbolTable, 
  EI := ErrorInstr, StdTypes, WL := Worklist;

CONST 
  assertion = TRUE;

CONST
  countElim = FALSE;
VAR
  counter: LONGINT;

CONST
  maxFoldingOpcode = Opc.geqstr;

  
(* NOTE: Order of states is relevant:
   stateUnreachable < stateNonConst < stateConst < stateUnclassified *)
   
CONST
  stateUnclassified = 4; (* result not known for now *)
  stateConst = stateUnclassified - 2; (* result is constant  *)
  stateNonConst = stateUnclassified - 3; (* result could never become constant *)
  stateUnreachable = stateUnclassified - 4; (* result is not computed at all, because it´s not reached *)
  
TYPE
  Lattice = POINTER TO LatticeDesc;
  LatticeDesc = RECORD (D.UsableDesc)
    state: LONGINT;
    const: D.Const;
  END;

VAR
  unclassifiedLattice: Lattice;
  nonConstLattice: Lattice;
  falseLattice, trueLattice: Lattice;
  unreachableLattice: Lattice;

PROCEDURE CheckConstSemantics* (instr: D.Instruction);
(* pre: `instr' has at least one operand, `instr' can't be folded into a
     constant *)
  VAR
    class: SHORTINT;
    opnd1, opnd2: D.Usable;
  BEGIN
    class := SHORT (instr. opcode DIV Opc.sizeClass);
    opnd1 := instr. opndList. arg;
    IF (instr. opndList. nextOpnd # NIL) THEN
      opnd2 := instr. opndList. nextOpnd. arg;
    ELSE
      opnd2 := NIL;
    END;
    IF (class = Opc.classDivInt) OR (class = Opc.classMod) THEN
      IF (opnd2 IS D.Const) & (opnd2(D.Const). int = 0) THEN
        EI.Err (instr, 351);         (* division by zero *)
      END;
    ELSIF (class = Opc.classDivReal) THEN 
      IF (opnd2 IS D.Const) & (opnd2(D.Const). real = 0.0) THEN
        EI.Err (instr, 351);         (* division by zero *)
      END;
    ELSIF (instr. opcode = Opc.boundIndex) THEN
      IF (opnd1 IS D.Const) & (opnd1(D.Const). int < 0) THEN
        EI.ErrOoR (instr, 354, 0, -1);
      END;
    END;
  END CheckConstSemantics;

PROCEDURE Foldable (instr: D.Instruction): BOOLEAN;
  VAR
    opc: INTEGER;
  BEGIN
    opc := instr. opcode;
    RETURN (opc >= Opc.baseConv) & (opc <= maxFoldingOpcode) OR
           (opc = Opc.boundIndex) OR
           (opc = Opc.boundRange) OR
           (opc = Opc.typeCast)
  END Foldable;

PROCEDURE ConstantFolding (instr: D.Instruction; opnd1, opnd2: D.Const; adaptType: BOOLEAN): D.Const;
(* Tries to fold `instr' with the two operands `opnd1' and `opnd2' into
   a constant. `opnd2' may be NIL for monadic operations. 
   If the tripple (instr, opnd1, opnd2) results in a constant, this
   constant is returned as the result, NIL otherwise.
   
   If `adaptType' then automatic type conversion is done.
   
   Pre: (instr. opcode >= Opc.baseConv) OR (instr. opcode = Opc.boundIndex) 
        OR (instr. opcode = Opc.boundRange), opnd1 # NIL 
*)
  VAR
    subClass, class: SHORTINT;
    resConst: D.Const;
    err: INTEGER;
    intRange: SHORTINT;
    destType: D.Struct;
    srcSubClass: SHORTINT;
    lreal: LONGREAL;
  
  PROCEDURE GetType (instr: D.Instruction; res: LONGINT): D.Struct;
  (* if `adaptType', then get smallest integer type which can
       hold the value `res', type of `instr' otherwise. *)
    VAR
      struct: D.Struct;
    BEGIN
      IF adaptType THEN
        struct := StdTypes.IntType (res)
      ELSE
        struct := instr. type
      END;
      ASSERT (struct # NIL); (* "no type for constant available" *)
      RETURN struct
    END GetType;
  
  PROCEDURE EvalMonadicIntOp (op: Int.MonadicOperator; opnd: D.Const): D.Const;
    VAR
      res: LONGINT;
      struct: D.Struct;
    BEGIN
      res := op (opnd. int, intRange, err);
      struct := GetType (instr, res);
      RETURN D.GetIntConst (res, struct);
    END EvalMonadicIntOp;

  PROCEDURE EvalDyadicIntOp (op: Int.DyadicOperator; opnd1, opnd2: D.Const): D.Const;
    VAR
      res: LONGINT;
      struct: D.Struct;
    BEGIN
      res := op (opnd1. int, opnd2. int, intRange, err);
      struct := GetType (instr, res);
      ASSERT (struct # NIL); (* "no type for constant available" *)
      RETURN D.GetIntConst (res, struct)
    END EvalDyadicIntOp;  
  
  PROCEDURE GetSetConst (set: SET): D.Const;
    BEGIN
      RETURN D.GetSetConst (set, instr. type)
    END GetSetConst;
  
  PROCEDURE SystemROT (x, n: D.Const; type: D.Struct): D.Const;
  (*  SIZE(type) = size of `type' on the machine the compiler runs on *)
    VAR
      li: LONGINT;
      in: INTEGER;
      si: SHORTINT;
      by: SYSTEM.BYTE;
      ch: CHAR;
    BEGIN
      IF adaptType & Sym.TypeInGroup (x. type, D.grpInteger) THEN
        (* convert argument to LONGINT, rotate, adjust type to smallest
           possible integer type *)
        li := SYSTEM.ROT (x. int, n. int);
        RETURN D.GetIntConst (li, StdTypes.IntType (li))
      END;
      
      CASE x. type. form OF
      (* the size of those types is always fixed to one byte (so no multibyte
         characters are permitted here...*)
      | D.strChar8:
        ch := CHR (x. int);
        RETURN D.GetIntConst (ORD (SYSTEM.ROT (ch, n. int)), type);
      | D.strByte:
        by := SYSTEM.VAL (SYSTEM.BYTE, CHR (x.int));
        ch := SYSTEM.VAL (CHAR, SYSTEM.ROT (by, n. int));
        
        IF (ORD (ch) > 127) THEN
          RETURN D.GetIntConst ((-256 + ORD (ch)), type);
        ELSE
          RETURN D.GetIntConst (ORD (ch), type);
        END;
      ELSE
        CASE x. type. size OF
        | SIZE(LONGINT):
          li := x. int;
          RETURN D.GetIntConst (SYSTEM.ROT (li, n. int), type);
        | SIZE(INTEGER):
          in := SHORT (x. int);
          in := SYSTEM.ROT (in, n. int);
          RETURN D.GetIntConst (in, type);
        | SIZE(SHORTINT):
          si := SHORT (SHORT (x. int));
          si := SYSTEM.ROT (si, n. int);
          RETURN D.GetIntConst (si, type);
        ELSE
          RETURN NIL;
        END;
      END;
    END SystemROT;
  
  PROCEDURE SystemLSH (x, n: D.Const; type: D.Struct): D.Const;
  (*  SIZE(type) = size of `type' on the machine the compiler runs on *)
    VAR
      li: LONGINT;
      in: INTEGER;
      si: SHORTINT;
      by: SYSTEM.BYTE;
      ch: CHAR;
    BEGIN
      IF adaptType & Sym.TypeInGroup (x. type, D.grpInteger) THEN
        (* convert argument to LONGINT, shift, adjust type to smallest
           possible integer type *)
        li := SYSTEM.LSH (x. int, n. int);
        RETURN D.GetIntConst (li, StdTypes.IntType (li))
      END;
      
      CASE x. type. form OF
      | D.strChar8:
        ch := CHR (x. int);
        RETURN D.GetIntConst (ORD (SYSTEM.LSH (ch, n. int)), type);
      | D.strByte:
        by := SYSTEM.VAL (SYSTEM.BYTE, CHR (x.int));
        ch := SYSTEM.VAL (CHAR, SYSTEM.LSH (by, n. int));
        
        IF (ORD (ch) > 127) THEN
          RETURN D.GetIntConst ((-256 + ORD (ch)), type);
        ELSE
          RETURN D.GetIntConst (ORD (ch), type);
        END;
      ELSE
        CASE x. type. size OF
        | SIZE(LONGINT):
          li := x. int;
          RETURN D.GetIntConst (SYSTEM.LSH (li, n. int), type);
        | SIZE(INTEGER):
          in := SHORT (x. int);
          in := SYSTEM.LSH (in, n. int);
          RETURN D.GetIntConst (in, type);
        | SIZE(SHORTINT):
          si := SHORT (SHORT (x. int));
          si := SYSTEM.LSH (si, n. int);
          RETURN D.GetIntConst (si, type);
        ELSE
          RETURN NIL;
        END;
      END;
    END SystemLSH;

  PROCEDURE ShortToReal (x: LONGREAL): REAL;
    BEGIN  (* perform SHORT(x) without causing a floating point exception *)
      IF StdTypes.ValidReal (x) THEN
        RETURN SHORT (x)
      ELSIF (x > 0) THEN
        RETURN MAX (REAL)
      ELSE
        RETURN MIN (REAL)
      END
    END ShortToReal;
  
  PROCEDURE TypeCast (arg: D.Const; dest: D.Struct): D.Const;
  (* note: type casts aren't checked for overflows; this procedure assumes that
           SIZE(LONGINT)=SIZE(REAL) *)
    VAR
      c: D.ConstDesc;
    BEGIN
      CASE dest. form OF
      | D.strBoolean..D.strHugeInt:
        CASE arg. type. form OF
        | D.strBoolean..D.strHugeInt:
          c. int := arg. int
        | D.strReal, D.strLongReal:  (* assume cast from REAL to LONGINT *)
          c. int := SYSTEM.VAL (LONGINT, ShortToReal (arg. real))
        | D.strSet8..D.strSet64:
          c. int := SYSTEM.VAL (LONGINT, arg. set)
        ELSE
          RETURN NIL
        END;
        RETURN D.GetIntConst (c. int, dest)
      | D.strReal, D.strLongReal:
        CASE arg. type. form OF
        | D.strBoolean..D.strHugeInt:  (* assume cast to REAL *)
          c. real := LONG (SYSTEM.VAL (REAL, arg. int))
        | D.strReal, D.strLongReal:
          c. real := arg. real
        | D.strSet8..D.strSet64:
          c. real := LONG (SYSTEM.VAL (REAL, arg. set))
        ELSE
          RETURN NIL
        END;
        RETURN D.GetRealConst (c. real, dest)
      | D.strSet8..D.strSet64:
        CASE arg. type. form OF
        | D.strBoolean..D.strHugeInt:
          c. set := SYSTEM.VAL (SET, arg. int)
        | D.strReal, D.strLongReal:  (* assume cast from REAL to SET *)
          c. set := SYSTEM.VAL (SET, ShortToReal (arg. real))
        | D.strSet8..D.strSet64:
          c. set := arg. set
        ELSE
          RETURN NIL
        END;
        RETURN D.GetSetConst (c. set, dest)
      ELSE
        RETURN NIL
      END
    END TypeCast;
  
  BEGIN
    IF assertion THEN ASSERT (Foldable (instr)); END;

    IF ~Foldable (instr) THEN (* test the precondition... *)
      RETURN NIL;
    END;
    
    resConst := NIL;
    subClass := SHORT(instr. opcode MOD Opc.sizeClass);
    class := SHORT(instr. opcode DIV Opc.sizeClass);
    err := -1;
    
    IF (instr. opcode = Opc.boundIndex) OR (instr. opcode = Opc.boundRange) THEN
      IF (0 <= opnd1. int) & (opnd1. int < opnd2. int) THEN
        (* index or set element within range, or instruction is disabled *)
        resConst := opnd1;
      ELSE (* index or set element out of range *)
        IF (instr. opcode = Opc.boundIndex) THEN
          EI.ErrOoR (instr, 354, 0, opnd2. int);
        ELSE (* (instr. opcode = Opc.boundRange) *)
          EI.ErrOoR (instr, 353, 0, opnd2. int);
        END;
      END;
    
    ELSIF (instr. opcode = Opc.typeCast) THEN
      resConst := TypeCast (instr. opndList. arg(D.Const), instr. type)
      
    ELSIF (class = Opc.classConv) THEN (* type conversions *)
      srcSubClass := SHORT (SHORT (opnd1. int)); (* source type to convert from *)
      destType := instr. type;
      IF (srcSubClass < Opc.subclR) THEN (* .. from integer type *)
        IF (subClass < Opc.subclR) THEN (* .. to integer type *)
          resConst := D.GetIntConst (opnd2. int, destType);
          IF Int.OutOfRange (resConst. int, subClass, err) THEN
            Sym.ErrT1 (instr. pos, 352, destType);
            (* constant not representable as target type *)
            (* get a legal constant value to continue folding *)
            resConst := D.GetIntConst (1, destType)  
          END
        ELSE (* .. to real type *)
          lreal := opnd2. int;
          IF (subClass = Opc.subclR) THEN  (* round to REAL *)
            resConst := D.GetRealConst (SHORT (lreal), destType)
          ELSE
            resConst := D.GetRealConst (lreal, destType)
          END
        END
      ELSIF (srcSubClass = Opc.subclR) OR (srcSubClass = Opc.subclD) THEN 
        (* .. from real type *)
        IF (subClass < Opc.subclR) THEN (* .. to integer type *)
          IF StdTypes.ValidInt (opnd2. real) THEN
            resConst := D.GetIntConst (ENTIER (opnd2. real), destType)
          ELSE
            Sym.ErrT1 (instr. pos, 352, destType);
            (* constant not representable as target type *)
            resConst := D.GetIntConst (1, destType)
          END
        ELSIF (subClass = Opc.subclR) THEN (* .. to single precision real *)
          IF StdTypes.ValidReal (opnd2. real) THEN
            resConst := D.GetRealConst (SHORT (opnd2. real), destType)
          ELSE
            Sym.ErrT1 (instr. pos, 352, destType);
            (* constant not representable as target type *)
            resConst := D.GetRealConst (1, destType);
          END
        ELSE (* .. to double precision real type, no overflow possible *)
          resConst := D.GetRealConst (opnd2. real, destType);
        END;
      END;
      
    ELSIF ((subClass = Opc.subclStr) OR
           (subClass = Opc.subclLStr)) THEN    (* string comparison *)
      IF assertion & Error.noerr THEN ASSERT (opnd1. type = opnd2. type); END;
      CASE class OF
      | Opc.classEql:
        resConst := Sym.GetBoolConst (D.CompareStrings (opnd1, opnd2) = 0);
      | Opc.classNeq:
        resConst := Sym.GetBoolConst (D.CompareStrings (opnd1, opnd2) # 0);
      | Opc.classLss:
        resConst := Sym.GetBoolConst (D.CompareStrings (opnd1, opnd2) < 0);
      | Opc.classLeq:
        resConst := Sym.GetBoolConst (D.CompareStrings (opnd1,  opnd2) <=0);
      | Opc.classGtr:
        resConst := Sym.GetBoolConst (D.CompareStrings (opnd1, opnd2) > 0);
      | Opc.classGeq:
        resConst := Sym.GetBoolConst (D.CompareStrings (opnd1,  opnd2) >=0);
      END;
            
    ELSIF (subClass = Opc.subclR) OR (subClass = Opc.subclD) THEN 
      (* reals go here *)
      IF assertion & Error.noerr & (opnd2 # NIL) THEN ASSERT (opnd1. type = opnd2. type); END;
      CASE class OF
      | Opc.classAdd, Opc.classSub, Opc.classMult, Opc.classDivReal, Opc.classNeg:
        CASE class OF
        | Opc.classAdd:
          lreal := opnd1. real + opnd2. real
        | Opc.classSub:
          lreal := opnd1. real - opnd2. real
        | Opc.classMult:
          lreal := opnd1. real * opnd2. real
        | Opc.classDivReal:
          IF (opnd2. real = 0.0) THEN
            lreal := 1; err := 351      (* division by zero *)
          ELSE
            lreal := opnd1. real / opnd2. real
          END;
        | Opc.classNeg:
          lreal := -opnd1. real
        END;
        IF (err < 0) &
           (LowLReal.IsInfinity (lreal) OR LowLReal.IsNaN (lreal) OR
            (subClass = Opc.subclR) & ~StdTypes.ValidReal (lreal)) THEN
          err := 350                     (* overflow *)
        END;
        IF (err < 0) THEN
          IF (subClass = Opc.subclR) THEN  (* round to REAL *)
            resConst := D.GetRealConst (SHORT (lreal), instr. type)
          ELSE
            resConst := D.GetRealConst (lreal, instr. type)
          END
        END
        
      | Opc.classEql:
        resConst := Sym.GetBoolConst (opnd1. real = opnd2. real);
      | Opc.classNeq:
        resConst := Sym.GetBoolConst (opnd1. real # opnd2. real);
      | Opc.classLss:
        resConst := Sym.GetBoolConst (opnd1. real < opnd2. real);
      | Opc.classLeq:
        resConst := Sym.GetBoolConst (opnd1. real <= opnd2. real);
      | Opc.classGtr:
        resConst := Sym.GetBoolConst (opnd1. real > opnd2. real);
      | Opc.classGeq:
        resConst := Sym.GetBoolConst (opnd1. real >= opnd2. real);
      END;
      
    ELSIF Sym.TypeInGroup (instr. type, D.grpSet) THEN  (* set operations *)
      IF assertion & Error.noerr & (opnd2 # NIL) &
         (class # Opc.classBitSet) &
         (class # Opc.classBitClear) &
         (class # Opc.classBitRange) &
         (class # Opc.classBitTest) THEN
        ASSERT (opnd1. type = opnd2. type); 
      END;
      CASE class OF
      | Opc.classInter:
        resConst := GetSetConst (opnd1. set * opnd2. set)
      | Opc.classSymDiff:
        resConst := GetSetConst (opnd1. set / opnd2. set)
      | Opc.classUnion:
        resConst := GetSetConst (opnd1. set + opnd2. set)
      | Opc.classDiff:
        resConst := GetSetConst (opnd1. set - opnd2. set)
      | Opc.classCompl:
        resConst := GetSetConst (-opnd1. set);
        
      | Opc.classEql:
        resConst := Sym.GetBoolConst (opnd1. set = opnd2. set);
      | Opc.classNeq:
        resConst := Sym.GetBoolConst (opnd1. set # opnd2. set);
        
      | Opc.classBitSet:
        resConst := GetSetConst(opnd1. set + {opnd2. int});
      | Opc.classBitClear:
        resConst := GetSetConst (opnd1. set - {opnd2. int});
      | Opc.classBitRange:
        resConst := GetSetConst ({opnd1. int .. opnd2. int});
      END
      
    ELSIF (subClass <= Opc.subclLU) THEN 
      (* integer, char, or boolean operations *)
      IF assertion & Error.noerr & (opnd2 # NIL) &
         (class # Opc.classLsh) & 
         (class # Opc.classRot) & 
         (class # Opc.classAsh) &
         (class # Opc.classBitTest) THEN
        ASSERT (opnd1. type = opnd2. type);
      END;
      IF adaptType & Sym.TypeInGroup (instr. type, D.grpInteger) THEN
        intRange := Opc.subclL;
      ELSE
        intRange := subClass; (* of instruction tells us the desired range *)
      END;
      CASE class OF
      | Opc.classAdd:
        resConst := EvalDyadicIntOp (Int.Add, opnd1, opnd2);
      | Opc.classSub:
        resConst := EvalDyadicIntOp (Int.Sub, opnd1, opnd2);
      | Opc.classMult:
        resConst := EvalDyadicIntOp (Int.Mult, opnd1, opnd2);
      | Opc.classDivInt:
        resConst := EvalDyadicIntOp (Int.Div, opnd1, opnd2);
      | Opc.classMod:
        resConst := EvalDyadicIntOp (Int.Mod, opnd1, opnd2);
      | Opc.classNeg:
        resConst := EvalMonadicIntOp (Int.Neg, opnd1);
      | Opc.classAbs:
        resConst := EvalMonadicIntOp (Int.Abs, opnd1);
      | Opc.classAsh:
        resConst := EvalDyadicIntOp (Int.Ash, opnd1, opnd2);
      | Opc.classCap:
        resConst := D.GetIntConst (SYSTEM.VAL (SHORTINT, CAP(SYSTEM.VAL (CHAR, SHORT (SHORT (opnd1. int))))), instr. type);
      | Opc.classOdd:
        resConst := Sym.GetBoolConst (ODD (opnd1. int));

      | Opc.classLsh:
        resConst := SystemLSH (opnd1, opnd2, instr. type);
      | Opc.classRot:
        resConst := SystemROT (opnd1, opnd2, instr. type);

      | Opc.classNot:
        resConst := Sym.GetBoolConst (opnd1. int = 0);
      
      | Opc.classEql:
        resConst := Sym.GetBoolConst (opnd1. int = opnd2. int);
      | Opc.classNeq:
        resConst := Sym.GetBoolConst (opnd1. int # opnd2. int);
      | Opc.classLss:
        resConst := Sym.GetBoolConst (opnd1. int < opnd2. int);
      | Opc.classLeq:
        resConst := Sym.GetBoolConst (opnd1. int <= opnd2. int);
      | Opc.classGtr:
        resConst := Sym.GetBoolConst (opnd1. int > opnd2. int);
      | Opc.classGeq:
        resConst := Sym.GetBoolConst (opnd1. int >= opnd2. int);

      | Opc.classBitTest:
        resConst := Sym.GetBoolConst (opnd2. int IN opnd1. set);
      END;
    END;
    
    IF (err # -1) THEN
      EI.Err (instr, err)
    END;
    RETURN resConst
  END ConstantFolding;

PROCEDURE TryConstantFolding*(instr: D.Instruction; adaptType: BOOLEAN): D.Const;
(* Tries to fold `instr' into a constant. If `instr' results in a constant,
   this constant is returned, NIL otherwise.
   
   If `adaptType' then automatic type conversion is done.
   
   Pre: instr. opcode >= Opc.baseConv, one or two operands available
*)
  VAR
    opnd1, opnd2: D.Const;
  BEGIN
    IF ~(instr. opndList. arg IS D.Const) OR
        ((instr. opndList. nextOpnd # NIL) & 
         ~(instr. opndList. nextOpnd. arg IS D.Const)) THEN
      (* instruction does not result in a constant *)
      RETURN NIL;
    END;
    IF ~assertion OR Foldable (instr) THEN
      opnd1 := instr. opndList. arg(D.Const);
      IF (instr. opndList. nextOpnd = NIL) THEN
        opnd2 := NIL;
      ELSE
        opnd2 := instr. opndList. nextOpnd. arg(D.Const);
      END;
      RETURN ConstantFolding (instr, opnd1, opnd2, adaptType);
    ELSE
      RETURN NIL;
    END;
  END TryConstantFolding;




PROCEDURE HasLattice (usable: D.Usable): BOOLEAN;
(* returns TRUE if `usable. info' is a valid lattice element *)
  BEGIN
    RETURN (usable. info # NIL) & (usable. info IS Lattice);
  END HasLattice;

PROCEDURE ConstLattice (const: D.Const): Lattice;
(* Returns the lattice element for the given constand `const'.
   If the lattice element for `const' is not yet set, then
   initialize and set it. *)
  VAR
    lattice: Lattice;
  BEGIN
    IF ~HasLattice (const) THEN
      (* lattice for this constant is not set, so set it. *)
      NEW (lattice);
      lattice. state := stateConst;
      lattice. const := const;
      const. info := lattice;
    END;
    RETURN const. info(Lattice);
  END ConstLattice;

PROCEDURE InitLattice (usable: D.Usable);
  VAR
    opnd: D.Opnd;
    result: D.Result;
    opcode: LONGINT;
    useCopy: D.Usable;
  BEGIN
    IF ~HasLattice (usable) THEN
      useCopy := usable;
      
      WITH useCopy: D.GlobalRegion DO
        useCopy. info := trueLattice;
        
      | useCopy: D.Region DO
        usable. info := unclassifiedLattice;
        opnd := useCopy. opndList;
        WHILE (opnd # NIL) DO
          InitLattice (opnd. arg);
          opnd := opnd. nextOpnd;
        END;
        
      | useCopy: D.Instruction DO
        opcode := useCopy. opcode;
        IF Foldable (useCopy) OR (opcode = Opc.gate) THEN
        (* Only those instructions could evaluate to constants by procedure `ConstantFolding'. 
          `gate' is a special case which depends on the classification of it´s corresponding merge instruction *)
          usable. info := unclassifiedLattice;
          ASSERT (useCopy. nextResult = NIL); (* those instructions only have one result: themself *)
        ELSE
          result := useCopy;
          WHILE (result # NIL) DO
            result. info := nonConstLattice;
            result := result. nextResult;
          END;
        END;
        
        (* init all of the instruction's operands *)
        opnd := useCopy. opndList;
        WHILE (opnd # NIL) DO
          InitLattice (opnd. arg);
          opnd := opnd. nextOpnd;
        END;
        
      | useCopy: D.Const DO
        usable. info := ConstLattice (useCopy);
        
      | useCopy: D.Object DO
        usable. info := nonConstLattice;
        
      ELSE
        usable. info := unclassifiedLattice;
      END;
    END;          
  END InitLattice;
  
  
PROCEDURE RegionInitLattices (reg: D.Region);
(* Initialize lattices of region `reg' and enclosed regions *)
  VAR
    instr: D.Instruction;
  BEGIN
    InitLattice (reg);
    instr := reg. instrList;
    WHILE (instr # NIL) DO
      WITH instr: D.Region DO
        RegionInitLattices (instr);
      ELSE
        InitLattice (instr);
      END;
      instr := instr. nextInstr;
    END;    
  END RegionInitLattices;
  

PROCEDURE LatticeOfGate (gate: D.Gate): Lattice;
  VAR
    merge: D.Merge;
    mergeLattice: Lattice;
    opnd: D.Opnd;
    const: D.Const;

  PROCEDURE ConstantInput (gate: D.Gate): D.Const;
  (* If all inputs of `gate' are the same constant, return it, NIL otherwise *)
    VAR
      opnd: D.Opnd;
      inputLattice: Lattice;
      const: D.Const;
    BEGIN
      opnd := gate. opndList. nextOpnd;
      inputLattice := opnd. arg. info(Lattice);
      
      IF (inputLattice. state = stateConst) THEN
        const := inputLattice. const;
        WHILE (opnd. nextOpnd # NIL) DO
          opnd := opnd. nextOpnd;
          inputLattice := opnd. arg. info(Lattice);
          IF (inputLattice. state # stateConst) OR (const # inputLattice. const) THEN
            RETURN NIL;
          END;
        END;
        RETURN const;
      END;
      
      RETURN NIL;
    END ConstantInput;
    
  BEGIN
    merge := gate. opndList. arg(D.Merge);
    mergeLattice := merge. info(Lattice);

    IF (merge. opcode = Opc.mergeLoop) THEN
      RETURN nonConstLattice;

    ELSE (* merge. opcode IN {Opc.mergeIf, Opc.mergeCond, mergeCase} *)
      IF (gate. info(Lattice). state > stateConst) THEN
      
        opnd := gate. opndList;
        WHILE (opnd # NIL) DO
          IF (opnd. arg. info = unclassifiedLattice) THEN
            RETURN unclassifiedLattice; (* stay top as long as at least one operand is top *)
          END;
          opnd := opnd. nextOpnd;
        END;
        
        IF (mergeLattice. state = stateConst) THEN (* constant alternative *)
          opnd := gate. NthOperand (SHORT(mergeLattice. const. int));
          RETURN opnd. arg. info(Lattice);
        ELSE
          const := ConstantInput (gate);
          IF (const # NIL) THEN
          (* all gate inputs denote the same constant, so the result of the gate itself is this constant *)
            RETURN ConstLattice (const);
          ELSE
            RETURN nonConstLattice; 
          END;
        END;
      ELSE
        RETURN gate. info(Lattice);
      END;
    END;
  END LatticeOfGate;


PROCEDURE LatticeOfMerge (merge: D.Merge): Lattice;

  PROCEDURE TakenCase (merge: D.Merge): Lattice;
    VAR
      opnd: D.Opnd;
      opndLat: Lattice;
    BEGIN
      ASSERT (merge. opcode = Opc.mergeCase);
      IF (merge. info(Lattice). state > stateConst) THEN
        opnd := merge. opndList;
        WHILE (opnd # NIL) DO
          opndLat := opnd. arg. info(Lattice);
          IF (opndLat = unclassifiedLattice) THEN
            RETURN unclassifiedLattice;
          ELSIF (opndLat = trueLattice) THEN (* all regions of mergeCase are mutually exclusive... *)
            RETURN ConstLattice (D.GetIntConst (opnd. OperandIndex() + 1, D.struct[D.strLongInt]));
          END;
          opnd := opnd. nextOpnd;
        END;
        RETURN nonConstLattice; 
      END;
      RETURN merge. info(Lattice);
    END TakenCase;
  
  PROCEDURE TakenMergeRegion (merge: D.Merge): Lattice;
    VAR
      opnd1, opnd2: D.Opnd;
      lat1, lat2: Lattice;
      takeRegion1, takeRegion2: D.Const;
      
    BEGIN
      ASSERT ((merge. opcode = Opc.mergeIf) OR (merge. opcode = Opc.mergeCond));

      takeRegion1 := D.GetIntConst (1, D.struct[D.strLongInt]);
      takeRegion2 := D.GetIntConst (2, D.struct[D.strLongInt]);
      
      opnd1 := merge. opndList;
      opnd2 := opnd1. nextOpnd;
      ASSERT (opnd2. nextOpnd = NIL);
      
      lat1 := opnd1. arg. info(Lattice);
      lat2 := opnd2. arg. info(Lattice);

      IF (lat1 = unclassifiedLattice) OR (lat2 = unclassifiedLattice) THEN
        RETURN unclassifiedLattice; (* still unclassified *)
      END;

      IF (lat1 = unreachableLattice) OR (lat1 = falseLattice) THEN
        IF (lat2 = unreachableLattice) OR (lat2 = falseLattice) OR opnd1. arg(D.Region). DominatesNR (opnd2. arg(D.Region)) THEN
          RETURN unreachableLattice;
        ELSE (* region 2 is taken, if at all *)
          RETURN ConstLattice (takeRegion2);
        END;
      END;

      IF (lat2 = unreachableLattice) OR (lat2 = falseLattice) THEN 
        IF opnd2. arg(D.Region). DominatesNR (opnd1. arg(D.Region)) THEN
          RETURN unreachableLattice;
        ELSE (* region 1 is taken, if at all *)
          RETURN ConstLattice (takeRegion1);
        END;
      END;
      
      IF (lat1 = trueLattice) THEN
        IF opnd1. arg(D.Region). region = opnd2. arg(D.Region). region THEN
          RETURN ConstLattice (takeRegion1);
        END;
      END;
      
      IF (lat2 = trueLattice) THEN
        IF opnd1. arg(D.Region). region = opnd2. arg(D.Region). region THEN
          RETURN ConstLattice (takeRegion2);
        END;
      END;
      
      
(*      IF (lat1 = trueLattice) THEN
        IF ~D.DominatesNR (opnd1. arg(D.Region), opnd2. arg(D.Region)) THEN
          RETURN ConstLattice (takeRegion1);
        END;
      END;

      IF (lat2 = trueLattice) THEN
        IF ~D.DominatesNR (opnd2. arg(D.Region), opnd1. arg(D.Region)) THEN
          RETURN ConstLattice (takeRegion2);
        END;
      END;
*)
      RETURN nonConstLattice; 
    END TakenMergeRegion;

  BEGIN
    IF (merge. opcode = Opc.mergeLoop) THEN (* do nothing with loops, yet... *)
      RETURN nonConstLattice;
    ELSIF (merge. opcode = Opc.mergeCase) THEN
      RETURN TakenCase (merge);
    ELSE (* merge. opcode IN {Opc.mergeIf, Opc.mergeCond} *)
      RETURN TakenMergeRegion (merge);
    END;
  END LatticeOfMerge;


PROCEDURE ComputeConstantResults (instr: D.Instruction): Lattice;
  VAR
    res, const1, const2: D.Const;
    opnd1, opnd2: D.Opnd;
  BEGIN
    ASSERT (Foldable (instr));

    res := NIL;
    const1 := NIL; const2 := NIL;
    opnd1 := NIL; opnd2 := NIL;
      
    opnd1 := instr. opndList;
    IF (opnd1. arg. info(Lattice). state = stateConst) THEN
      const1 := opnd1. arg. info(Lattice). const;
    END;
    
    opnd2 := instr. opndList. nextOpnd;
    IF (opnd2 # NIL) THEN
      IF (opnd2. arg. info(Lattice). state = stateConst) THEN 
        const2 := opnd2. arg. info(Lattice). const;
      END;
    END;
  
    IF (D.instrIsDisabled IN instr. flags) & (const1 # NIL) & (const2 = NIL) & ((instr. opcode = Opc.boundIndex) OR (instr. opcode = Opc.boundRange)) THEN
      (* disabled boundIndex or boundRange instruction with constant first operand,
         but non constant second operand *)
      IF (0 <= const1. int) THEN
        RETURN ConstLattice (const1);
      ELSE (* index or set element out of range *)
        IF (instr. opcode = Opc.boundIndex) THEN
          EI.ErrOoR (instr, 354, 0, -1);
        ELSE (* (instr. opcode = Opc.boundRange) *)
          EI.ErrOoR (instr, 353, 0, -1);
        END;
      END;
      
    ELSIF ((opnd1 = NIL) OR (const1 # NIL)) & ((opnd2 = NIL) OR (const2 # NIL)) THEN
      res := ConstantFolding (instr, const1, const2, FALSE);
      IF (res # NIL) THEN
        RETURN ConstLattice (res);
      END;
    END;
        
    RETURN nonConstLattice;
  END ComputeConstantResults;

PROCEDURE LatticeOfGuard (guard: D.Guard): Lattice;
  VAR
    const: D.Const;
    opndLattice: Lattice;
    res: BOOLEAN;
    range: D.Opnd;
  BEGIN
    opndLattice := guard. opndList. arg. info(Lattice);

    IF (guard. opcode = Opc.guardGreg) THEN
      RETURN guard. info(Lattice);
      
    ELSIF (opndLattice = unreachableLattice) THEN
      RETURN unreachableLattice;
      
    ELSIF (opndLattice. state > stateConst) THEN
      IF (guard. info(Lattice). state < opndLattice. state) THEN
        RETURN guard. info(Lattice);
      ELSE
        RETURN opndLattice;
      END;

    ELSIF (guard. opcode = Opc.guardCase) THEN
      IF (opndLattice. state = stateConst) THEN (* all other operands must be constant ranges! *)
        res := FALSE;
        const := opndLattice. const;
        range := guard. opndList. nextOpnd;
        REPEAT
          res := res OR ((range. arg(D.Const). int <= const. int) & (const. int <= range. arg(D.Const). int2));
          range := range. nextOpnd;
        UNTIL res OR (range = NIL);
        const := Sym.GetBoolConst (res);
        RETURN ConstLattice (const);
      END;
      
    ELSIF ((guard. opcode = Opc.guardTrue) OR (guard. opcode = Opc.guardFalse)) THEN 
      IF (opndLattice. state = stateConst) THEN
        IF assertion THEN ASSERT ((opndLattice = trueLattice) OR (opndLattice = falseLattice)); END;
        const := Sym.GetBoolConst ((guard. opcode = Opc.guardTrue) = (opndLattice = trueLattice));
        RETURN ConstLattice (const);
      END;
    END;
    
    RETURN nonConstLattice;
  END LatticeOfGuard;


PROCEDURE NewLattice (instr: D.Instruction): Lattice;
  VAR
    opnd1, opnd2: D.Opnd;
    lat1, lat2: Lattice;
  BEGIN
    IF (instr. region. info = falseLattice) OR (instr. region. info = unreachableLattice) THEN
      (* instruction will be never executed, so set to unreachable *)
      RETURN unreachableLattice;
    ELSIF (instr. info = nonConstLattice) THEN
      RETURN nonConstLattice;
    ELSIF (instr. info = unreachableLattice) THEN
      RETURN unreachableLattice;
      
    ELSIF (instr IS D.Gate) THEN
      RETURN LatticeOfGate (instr(D.Gate));
    ELSIF (instr IS D.Merge) THEN
      RETURN LatticeOfMerge (instr(D.Merge));
    ELSIF (instr IS D.Guard) THEN
      RETURN LatticeOfGuard (instr(D.Guard));
    ELSE

      IF ((instr. opcode = Opc.boundIndex) OR (instr. opcode = Opc.boundRange)) & (D.instrIsDisabled IN instr. flags) THEN
        IF (instr. opndList. arg. info(Lattice). state = stateConst) THEN
          RETURN ComputeConstantResults (instr);
        ELSE
          RETURN instr. opndList. arg. info(Lattice);
        END;

      ELSIF Foldable (instr) THEN
        (* `instr' has at most two operands and at least one operand,
           exceptions are string comparisons, which have four operands, of which only the first two are relevant vor constant determination *)
        opnd1 := instr. opndList;
        opnd2 := instr. opndList. nextOpnd;
        
        lat1 := opnd1. arg. info(Lattice);
        lat2 := NIL;
        IF (opnd2 # NIL) THEN
          lat2 := opnd2. arg. info(Lattice);
        END;

        IF (lat1. state = stateConst) & ((lat2 = NIL) OR (lat2. state = stateConst)) THEN
          RETURN ComputeConstantResults (instr);
        ELSIF (lat1 = unreachableLattice) OR (lat2 = unreachableLattice) THEN
          RETURN unreachableLattice;
        ELSIF (lat1 = nonConstLattice) OR (lat2 = nonConstLattice) THEN
          RETURN nonConstLattice;
        ELSE
          RETURN unclassifiedLattice;
        END;
      ELSE
        RETURN nonConstLattice;
      END;
    END;
  END NewLattice;

PROCEDURE UsingHook (used: D.Result; instr: D.Instruction): BOOLEAN;
(* This procedure is called by `Worklist.AddUsingInstr' *)
  BEGIN
    RETURN (instr. info # unreachableLattice);
  END UsingHook;

 
PROCEDURE ConstPropagation* (greg: D.Region);
  VAR
    worklist: WL.Worklist;
    instr: D.Instruction;
    iInstr: D.Info;
    newLattice: Lattice;
    result: D.Result;


  PROCEDURE ReplaceGatesByArgument (merge: D.Merge);
  (* Visit all gates with `merge' as their first argument and replace
     their uses by their operand at position `takenPos'. 
     The gates will be deleted after replacement is done.
     Remember that the index of `merge' within a gate is always `0'.
     The indexing of arguments is described in `Data.NthArgument'. *)
    VAR
      use, nextUse: D.Opnd;
      takenPos: LONGINT;
    BEGIN
      takenPos := merge. info(Lattice). const. int;
      use := merge. useList;
      WHILE (use # NIL) DO
        nextUse := use. nextUse;
        IF (use. instr IS D.Gate) THEN
          (* replace the gate *)
          use. instr. ReplaceUses (use. instr. NthArgument (SHORT(takenPos)));
          use. instr. Delete();
          IF countElim THEN INC (counter); END;
        END;
        use := nextUse;
      END;      
    END ReplaceGatesByArgument;    

  PROCEDURE ReplaceByConstants (region: D.Region);
    VAR
      instr, nextInstr: D.Instruction;
      instrLattice: Lattice;
    BEGIN
      instr := region. instrList;
      WHILE (instr # NIL) DO
        IF assertion THEN ASSERT (instr. info # unclassifiedLattice); END;
        nextInstr := instr. nextInstr;
        instrLattice := instr. info(Lattice);
        IF (instrLattice = unreachableLattice) THEN
          instr.Delete ();
        ELSE
          WITH instr: D.Merge DO
            ReplaceByConstants (instr);
            IF (instr. info(Lattice). state = stateConst) THEN
              ReplaceGatesByArgument (instr);
            END;
          | instr: D.Region DO
            ReplaceByConstants (instr);
          ELSE (* no region *)
            IF (instrLattice. state = stateConst) THEN
              (* instruction evalutates to a constant, so replace all it´s uses by the corresponding constant. *)
              instr. ReplaceUses (instrLattice. const);
              instr.Delete ();
              IF countElim THEN INC (counter); END; 
            END;
          END;
        END;
        instr := nextInstr;
      END;
    END ReplaceByConstants;
  
  PROCEDURE ReplaceRegions (region: D.Region);
    VAR
      changed: BOOLEAN;
      replaceRegion: D.Region;
        
  PROCEDURE FindRegionToReplace (region: D.Region);
  
  (* start with/find innermost region ... *)
    VAR
      walk: D.Region;
    BEGIN
      walk := region. regionList;
      WHILE (walk # NIL) & (replaceRegion = NIL) DO
        FindRegionToReplace (walk);
        walk := walk. nextRegion;
      END;
        
      IF (replaceRegion = NIL) THEN
        walk := region. regionList;
        WHILE (walk # NIL) & (replaceRegion = NIL) DO
          IF (walk IS D.Merge) & (walk. info(Lattice). state = stateConst) THEN
          (* only those regions are interesting for us... *)
            replaceRegion := walk;
(*        ELSIF (walk. info = unreachableLattice) THEN
          replaceRegion := walk; ...
*)          
          END;
          walk := walk. nextRegion;
        END;
      END;
    END FindRegionToReplace;

    PROCEDURE ReplaceSingleRegion (merge: D.Merge);
      VAR
        opnd: D.Opnd;
        replacement: D.Region;
      BEGIN
        IF (merge. info (Lattice). state = stateConst) THEN
          changed := TRUE;
            
          (* find replacement region *)
          opnd := merge. NthOperand (SHORT(merge. info(Lattice). const. int - 1));
          replacement := opnd. arg(D.Region);
            
          (* Move all instructions into the replacement region and replace merge by replacement *)
(*          ReplaceGatesByArgument (merge); ... is already done in the first phase of replacement! *)
          replacement. MoveInstructions (merge);
          merge. ReplaceUses (replacement);
            
          (* delete all used regions *)
          opnd := merge. opndList;
          WHILE (opnd # NIL) DO
            IF (opnd. arg # replacement) THEN
              opnd. arg(D.Instruction). Delete();
            END;
            opnd := opnd. nextOpnd;
          END;
            
          (* delete the merge itself *)           
          merge. Delete(); 

          (* if replacement region was always taken... *)
          IF (replacement. info = trueLattice) THEN
            replacement. region. MoveInstructions (replacement); 
            replacement. ReplaceUses (replacement. region);
            replacement. Delete();
          END;
        END;
      END ReplaceSingleRegion;
      
    
    PROCEDURE ReplaceConstantRegions (region: D.Region);
      VAR
        walk, next: D.Region;
        merge: D.Merge;
      BEGIN
        walk := region. regionList;
        WHILE (walk # NIL) DO
          next := walk. nextRegion;
          IF (walk. opcode = Opc.mergeLoop) &
             ((walk. opndList. nextOpnd. arg. info(Lattice) = unreachableLattice) OR 
              (walk. opndList. nextOpnd. arg. info(Lattice) = falseLattice)) THEN
            walk. region. MoveInstructions (walk);
            walk. info := ConstLattice (D.GetIntConst (1, D.struct[D.strLongInt]));
            ReplaceGatesByArgument (walk(D.Merge));
            walk. info := nonConstLattice;
            walk. ReplaceUses (walk. opndList. arg);
            walk. Delete();
          END;
          ReplaceConstantRegions (walk);
          IF (walk. info = trueLattice) THEN
(*            merge := Opc.RegionMerge (walk); ... it can happen, that a region is always taken, but the corresponding "merge" instruction is not always reached by the path through the region "walk", as the region "walk" could be enclosed in another region which is not always taken (e.g. the "merge-cond" constructs for the "&" operator) *)
            walk. region. MoveInstructions (walk);
            walk. ReplaceUses (walk. region);
            walk. Delete();
            changed := TRUE;
          ELSIF (walk. info = falseLattice) THEN
            merge := walk. RegionMerge();
(*            ASSERT (merge = NIL);  *)
            IF (merge # NIL) THEN walk. info := nonConstLattice; RETURN; END; 
            walk. Delete();
            changed := TRUE;
          ELSIF (walk. info = unreachableLattice) THEN (* unreachable region is part of merge... *)
(*            merge := Opc.RegionMerge (walk);
            ASSERT (merge = NIL); 
... *)            
          END;
          walk := next;
        END;
      END ReplaceConstantRegions;
    
    BEGIN
      REPEAT
        changed := FALSE;
        replaceRegion := NIL; FindRegionToReplace (region);  
        IF (replaceRegion # NIL) THEN
          ReplaceSingleRegion (replaceRegion(D.Merge));
        END;
      UNTIL ~changed; 


      REPEAT
        changed := FALSE;
        ReplaceConstantRegions (region);
      UNTIL ~changed;
    END ReplaceRegions;

   PROCEDURE MarkUnreachable (region: D.Region);
    (* Mark all instruction within `region' and enclosed regions as 
       "unreachable", i.e. they will never be executed.
       Also, add all uses of the marked regions to the worklist. *)
    VAR
      walk: D.Instruction;
      res: D.Result;
    BEGIN
      walk := region. instrList;
      WHILE (walk # NIL) DO

        res := walk;
        WHILE (res # NIL) DO
          res. info := unreachableLattice;
          res := res. nextResult;
        END;
        
        IF (walk IS D.Region) THEN
          worklist.AddUsingInstr (walk, UsingHook); 
          MarkUnreachable (walk(D.Region));
        END;

        walk := walk. nextInstr;
      END;
    END MarkUnreachable;


  PROCEDURE InitialWorklist (region: D.Region; add: BOOLEAN);
  (* Initialize lattice values for all instructions contained
     in `region'. Also, init lattice elements for embeded region. *)
    VAR
      instr: D.Instruction;
    BEGIN
      instr := region. instrList;
      WHILE (instr # NIL) DO
        IF add THEN
          IF (instr. info(Lattice) # unreachableLattice) THEN
            worklist.AddTail (instr);
          ELSE
            worklist.AddUsingInstr (instr, UsingHook);
          END;
        END;
        IF (instr IS D.Region) THEN
          InitialWorklist (instr(D.Region), FALSE);
        END;
        instr := instr. nextInstr;
      END;
    END InitialWorklist; 

  
  PROCEDURE AssertCorrectMarking (region: D.Region);
    VAR
      walk: D.Instruction;
    BEGIN
      walk := region. instrList;
      WHILE (walk # NIL) DO
        IF ~(walk. info(Lattice). state <= stateConst) THEN
          O.String ("Incorrect marking of ´"); GSA.WrOpcode (walk. opcode); O.String ("´ : "); O.LongInt (walk. info(Lattice). state, 0); O.Ln;
        END;
        ASSERT (walk. info(Lattice). state <= stateConst);        
        WITH walk: D.Region DO
          AssertCorrectMarking (walk);
        ELSE
        END;
        walk := walk. nextInstr;
      END;
    END AssertCorrectMarking;
  
  
  BEGIN
    falseLattice := ConstLattice (Sym.constFalse);
    trueLattice := ConstLattice (Sym.constTrue);

    greg. ClearInfo (0);
    greg(D.GlobalRegion). NumberDominanceTree();

    RegionInitLattices (greg);
    worklist.Init;

    (* Put all instructions of region onto the worklist and
       initialize their lattice elements. *)
    InitialWorklist (greg, TRUE);
    
    WHILE ~worklist.IsEmpty() DO
      (* fetch `instr' from `worklist' *)
      iInstr := worklist. GetHead ();
      worklist.RemoveHead;
      instr := iInstr(D.Instruction); 
      
      (* get the new lattice element for `instr' *)
      newLattice := NewLattice (instr);   
      
      IF (newLattice. state > instr. info(Lattice). state) THEN
        O.String ("Illegal lattice state change:"); O.LongInt (instr. info(Lattice). state,0);
        O.String (" to ");  O.LongInt (newLattice. state,0);
        O.String (" for: "); GSA.WrOpcode (instr. opcode); O.Ln;
      END;
      
      ASSERT (newLattice. state <= instr. info(Lattice). state);
      
      IF (newLattice. state < instr. info(Lattice). state) THEN
        (* lattice state changed, so all using instructions must
           be evaluated once more, since their lattice state may
           change also with the new information collected *)
        instr. info := newLattice;
        
        result := instr;
        WHILE (result # NIL) DO
          worklist.AddUsingInstr (result, UsingHook);
          result := result. nextResult;
        END;
        
        IF (instr IS D.Region) THEN
          IF (newLattice = unreachableLattice) THEN
          (* do nothing here *)
          ELSIF (newLattice = falseLattice) THEN
            (* mark all contained instructions as "unreachable", add uses of unreachable
               regions to the worklist. *)
            MarkUnreachable (instr(D.Region));
          ELSE
            (* This region (`instr') could still be executed, so inspect it later again *)
            worklist.AddInstr (instr(D.Region), NIL);
          END;
        END;
      END;
    END;


    IF assertion THEN AssertCorrectMarking (greg); END;
    
    (* Do the replacement of instructions by constants, 
       also eliminate unreached regions *)
    ReplaceByConstants (greg);
    ReplaceRegions (greg); 

    greg. ClearInfo (0);
  END ConstPropagation;


PROCEDURE TerminationProc;
  BEGIN
    IF countElim THEN O.String ("Number of eliminated instructions by ConstantFolding: "); O.LongInt (counter,0 ); O.Ln; END;
  END TerminationProc;


BEGIN
  counter := 0;
  Termination.RegisterProc (TerminationProc); 

  (* Initialize global lattice elements. *)
  NEW (unclassifiedLattice);
  NEW (nonConstLattice);
  NEW (unreachableLattice);
  unclassifiedLattice. state := stateUnclassified;
  nonConstLattice. state := stateNonConst;
  unreachableLattice. state := stateUnreachable;
END ConstPropagation.
