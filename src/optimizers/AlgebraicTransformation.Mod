(* 	$Id: AlgebraicTransformation.Mod,v 1.18 1999/03/19 20:39:13 acken Exp $	 *)
MODULE AlgebraicTransformation;
(*  Algebraic transformation
    Copyright (C) 1995/1996  Juergen Zimmermann

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
For the scope of this module a conversion of expression E into an
expression E' is an algebraic transformation if:
  1) E' calculates the same result as E
  2) E' raises the same exceptions that E would have raised
  3) E' is simpler than E
Point 2) prevents any transformations that drop execeptions.
E.g. `-a+b' can only be tranformed into `b-a' if it is known that `-a'
does not overflow (ie, if overflow checking is disabled or if it's
known that a doesn't equal MAX).
A simpler calculation is one that drops an instruction altogether or
transforms a dyadic instruction into a monadic one.

ATTENTION: Have a look at the comment of `GetMinMax'. *)  


IMPORT
  SYSTEM, O := Out,
  D := Data, Sym := SymbolTable, Opc := Opcode,
  WL := Worklist, Types := StdTypes;

CONST
  debug = FALSE;
  

PROCEDURE GetZero* (type: D.Struct): D.Const;
  BEGIN
    IF Sym.TypeInGroup (type, D.grpInteger) THEN
      RETURN D.GetIntConst (0, type)
    ELSIF Sym.TypeInGroup (type, D.grpReal) THEN
      RETURN D.GetRealConst (0.0, type)
    ELSIF Sym.TypeInGroup (type, D.grpSet) THEN
      RETURN D.GetSetConst ({}, type)
    ELSE
      CASE type. form OF
      | D.strBoolean: RETURN Sym.constFalse
      | D.strChar8, D.strChar16: RETURN D.GetIntConst (0, type)
      ELSE
        RETURN NIL
      END
    END
  END GetZero;

PROCEDURE GetOne* (type: D.Struct): D.Const;
  BEGIN
    IF Sym.TypeInGroup (type, D.grpInteger) THEN
      RETURN D.GetIntConst (1, type)
    ELSIF Sym.TypeInGroup (type, D.grpReal) THEN
      RETURN D.GetRealConst (1.0, type)
    ELSIF (type. form = D.strSet8) THEN
      RETURN D.GetSetConst ({Types.minSet8..Types.maxSet8}, type)
    ELSIF (type. form = D.strSet16) THEN
      RETURN D.GetSetConst ({Types.minSet16..Types.maxSet16}, type)
    ELSIF (type. form = D.strSet32) THEN
      RETURN D.GetSetConst ({Types.minSet32..Types.maxSet32}, type)
    ELSE
      CASE type. form OF
      | D.strBoolean: RETURN Sym.constTrue
      | D.strChar8, D.strChar16: RETURN D.GetIntConst (1, type)
      ELSE
        RETURN NIL
      END
    END
  END GetOne;

PROCEDURE Transform* (reg: D.Region);
  VAR
    worklist: WL.Worklist;
    iInstr: D.Info;
    instr: D.Instruction;
    subClass, class: INTEGER;
    replacement: D.Usable;

  PROCEDURE InitialWorklist (region: D.Region);
  (* Add all instructions of `region' to worklist. *)
    VAR
      instr: D.Instruction;
    BEGIN
      instr := region. instrList;
      WHILE (instr # NIL) DO
        worklist.AddTail (instr);
        IF (instr IS D.Region) THEN
          InitialWorklist (instr(D.Region));
        END;
        instr := instr. nextInstr;
      END;
    END InitialWorklist; 
  
  PROCEDURE BooleanResult (instr: D.Instruction): D.Usable;
  (* Handle all boolean expressions *)
    VAR
      opnd1, opnd2: D.Opnd;
      opnd1Instr: D.Instruction;
      opnd1InstrClass: INTEGER;
      replacement: D.Usable;
    
    PROCEDURE AllUsesAreNegations (instr: D.Instruction): BOOLEAN;
      VAR
        use: D.Opnd;
      BEGIN
        use := instr. useList;
        WHILE (use # NIL) & (use. instr. opcode = Opc.notsu) DO
          use := use. nextUse;
        END;
        RETURN (use = NIL);
      END AllUsesAreNegations;
  
    PROCEDURE AllUsesAreGuards (instr: D.Instruction): BOOLEAN;
      VAR
        use: D.Opnd;
      BEGIN
        use := instr. useList;
        WHILE (use # NIL) & (use. instr IS D.Guard) DO
          use := use. nextUse;
        END;
        RETURN (use = NIL);
      END AllUsesAreGuards;
    
    PROCEDURE NegateGuards (instr: D.Instruction);
    (* pre: instr. opcode = Opc.notSU *)
      VAR
        use, nextUse: D.Opnd;
      BEGIN
        use := instr. useList;
        WHILE (use # NIL) DO
          nextUse := use. nextUse;
          IF (use. instr IS D.Guard) THEN
            IF (use. instr. opcode = Opc.guardTrue) THEN
              use. instr. opcode := Opc.guardFalse;
              use. instr. opndList. ReplaceOperand (instr. opndList. arg);
            ELSIF (use. instr. opcode = Opc.guardFalse) THEN
              use. instr. opcode := Opc.guardTrue;
              use. instr. opndList. ReplaceOperand (instr. opndList. arg);
            END;
          END;
          use := nextUse;
        END;
      END NegateGuards;    
    
    BEGIN
      opnd1 := instr. opndList;
      opnd2 := opnd1. nextOpnd;
      replacement := NIL;
      
      IF (class = Opc.classNeg) THEN (* ... *)
        O.String ("AlgebraicTransformation:* error in frontend: conversion `classNeg -> classNot' performed"); O.Ln;
        instr. opcode := (Opc.classNot * Opc.sizeClass) + subClass;
        class := Opc.classNot;
        HALT (1);
      END;
      
      CASE class OF
      | Opc.classOdd:
      | Opc.classNot:
        IF AllUsesAreNegations (instr) THEN
          (* do nothing here...*)
        ELSIF AllUsesAreGuards (instr) THEN
          (* rework guards... *)
          NegateGuards (instr);
        ELSIF (opnd1. arg IS D.Instruction) THEN
          opnd1Instr := opnd1. arg(D.Instruction);
          opnd1InstrClass := (opnd1Instr. opcode DIV Opc.sizeClass);
          CASE opnd1InstrClass OF
          | Opc.classNot:
            worklist.AddUsingInstr (instr, NIL);
            instr. ReplaceUses (opnd1Instr. opndList. arg);
(*          | Opc.classEql: (* ... *)
          | Opc.classNeq:
          | Opc.classLss:
          | Opc.classLeq:
          | Opc.classGtr:
          | Opc.classGeq:
*)          
          ELSE
          END;
        END;
(* ...      
  IF (instr ist Negation) THEN
    IF (instr wird nur in Negationen verwendet) THEN
      nix tun
    ELSIF (opnd ist Negation) THEN
      alle uses von instr mit opnd vom opnd ersetzen 
    ELSIF (alle uses von instr guards) THEN
      guards aendern ??? Muessen alle `uses' guards sein? Koennen nicht auch nur manche guards sein? Wuerde die Freiheiten erhoehen.
    ELSIF (opnd ist vergleich) THEN
      neuen vergleich einfuegen, alle uses darauf umstellen
    ELSE
      nix tun
    END
  END
*)
      | Opc.classBitTest:
      ELSE

      END;
      RETURN replacement;
    END BooleanResult;

  PROCEDURE RemoveNeutralOpnd (instr: D.Instruction): D.Usable;
    VAR
      const: D.Const;
    BEGIN
      CASE (instr. opcode DIV Opc.sizeClass) OF
      | Opc.classAdd, Opc.classSub, 
        Opc.classUnion, Opc.classDiff, Opc.classSymDiff:
        const := GetZero (instr. type);
      | Opc.classMult, Opc.classDivInt, Opc.classDivReal , Opc.classInter:
        const := GetOne (instr. type);
      ELSE
        const := NIL;
      END;
      IF (const # NIL) THEN
        IF (instr. opndList. arg = const) & Opc.Commutative (instr. opcode) THEN
          RETURN instr. opndList. nextOpnd. arg;
        ELSIF (instr. opndList. nextOpnd. arg = const) THEN
          RETURN instr. opndList. arg;
        END;
      END;
      
      CASE (instr. opcode DIV Opc.sizeClass) OF
      | Opc.classMult, Opc.classInter:
        const := GetZero (instr. type);
        IF ((instr. opndList. arg = const) OR 
            (instr. opndList. nextOpnd. arg = const)) THEN
          RETURN const;
        END
      ELSE
        const := NIL;
      END;
                  
      RETURN NIL;
    END RemoveNeutralOpnd;
  
  PROCEDURE ArithmTransform (instr: D.Instruction): D.Usable;
    VAR
      replacement: D.Usable;
      posOpnd, negOpnd: D.Opnd;
      minusOne: D.Const;
      opnd1, opnd2: D.Opnd;
      class, subClass: INTEGER;
    
    PROCEDURE PowerOfTwo (int: LONGINT): LONGINT;
    (* Returns -1 if `int' isn't a power of 2, otherwise returns the value 
       `x' for `2^x = int'.  *)
      VAR
        c: LONGINT;
      BEGIN
        IF (int > 0) THEN
          c := 0;
          WHILE ~ODD (int) DO
            int := int DIV 2;
            INC (c)
          END;
          IF (int = 1) THEN
            RETURN c
          END
        END;
        RETURN -1
      END PowerOfTwo;
    
    PROCEDURE ReplaceMod (subcl: INTEGER; arg: D.Usable; 
                          mask: LONGINT): D.Instruction;
      VAR
        form: SHORTINT;
        type: D.Struct;
        repl, cast: D.Instruction;
      BEGIN
        CASE subcl OF
        | Opc.subclS: form := D.strSet8
        | Opc.subclI: form := D.strSet16
        | Opc.subclL: form := D.strSet32
        | Opc.subclLL: form := D.strSet64
        END;
        type := D.struct[form];
        repl := instr. region. CreateInstruction (Opc.baseInter+D.OperatorSubclass (NIL, form), type, instr. pos);
        cast := instr. region. CreateTypeCast (arg, type);
        repl. Operand (cast);
        repl. Operand (D.GetSetConst (SYSTEM.VAL (SET, mask), type));
        RETURN instr. region. CreateTypeCast (repl, instr. type)
      END ReplaceMod;
    
    BEGIN
      class := instr. opcode DIV Opc.sizeClass;
      subClass := instr. opcode MOD Opc.sizeClass;
      replacement := NIL;
      
      opnd1 := instr. opndList;
      IF (opnd1 # NIL) THEN
        opnd2 := opnd1. nextOpnd;
      ELSE
        opnd2 := NIL;
      END;
            
      CASE class OF
      | Opc.classNeg:
        IF (opnd1. arg IS D.Instruction) & 
           ((opnd1. arg(D.Instruction). opcode DIV Opc.sizeClass) = Opc.classNeg) THEN
          (* --a == a *)
          (* ... overflow checking for integers... *)
          replacement := opnd1. arg(D.Instruction). opndList. arg; 
        END;
      | Opc.classSub:
        IF (opnd1. arg IS D.Const) & (opnd1. arg = GetZero (instr. type)) THEN
          (* (0 - a) = -a *)
          replacement := instr. region. CreateInstruction ((Opc.classNeg * Opc.sizeClass) + subClass, instr. type, instr. pos);
          replacement(D.Instruction). Operand (opnd2. arg)
        END;
      | Opc.classAdd:
        posOpnd := NIL;
        negOpnd := NIL;
        IF (opnd1. arg IS D.Instruction) & ((opnd1. arg(D.Instruction). opcode DIV Opc.sizeClass) = Opc.classNeg) THEN
          negOpnd := opnd1;
          posOpnd := opnd2;
        ELSIF (opnd2. arg IS D.Instruction) & ((opnd2. arg(D.Instruction). opcode DIV Opc.sizeClass) = Opc.classNeg) THEN
          negOpnd := opnd2;
          posOpnd := opnd1;
        END;
        IF (posOpnd # NIL) & (negOpnd # NIL) THEN
          (* a + (-b) => a - b *)
          replacement := instr. region. CreateInstruction ((Opc.classSub * Opc.sizeClass) + subClass, instr. type, instr. pos);
          replacement(D.Instruction). Operand (posOpnd. arg);
          replacement(D.Instruction). Operand (negOpnd. arg(D.Instruction). opndList. arg);
      END;

      | Opc.classMult:
        IF Sym.TypeInGroup (instr. type, D.grpInteger) THEN
          minusOne := D.GetIntConst (-1, instr. type);
        ELSIF Sym.TypeInGroup (instr. type, D.grpReal) THEN
          minusOne := D.GetRealConst (-1.0, instr. type);
        ELSE
          minusOne := NIL;
        END;
        IF (minusOne # NIL) & ((opnd1. arg = minusOne) OR (opnd2. arg = minusOne)) THEN
          replacement := instr. region. CreateInstruction ((Opc. classNeg * Opc.sizeClass) + subClass, instr. type, instr. pos);
          IF (opnd1. arg = minusOne) THEN
            replacement(D.Instruction). Operand (opnd2. arg);
          ELSE
            replacement(D.Instruction). Operand (opnd1. arg);
          END;
        END;
        
        IF (replacement = NIL) & (subClass < Opc.subclR) THEN
          (* replace multiplication by power of two with an arithmetic shift *)
          IF (opnd2. arg IS D.Const) & 
             (PowerOfTwo (opnd2. arg(D.Const). int) >= 0) THEN
            replacement := instr. region. CreateInstruction (Opc.baseAsh + subClass, instr. type, instr. pos);
            replacement(D.Instruction). Operand (opnd1. arg);
            replacement(D.Instruction). Operand (D.GetIntConst (PowerOfTwo (opnd2. arg(D.Const). int),
                                      D.struct[D.strShortInt]))
          ELSIF (opnd1. arg IS D.Const) & 
                (PowerOfTwo (opnd1. arg(D.Const). int) >= 0) THEN
            replacement := instr. region. CreateInstruction (Opc.baseAsh + subClass, instr. type, instr. pos);
            replacement(D.Instruction). Operand (opnd2. arg);
            replacement(D.Instruction). Operand (D.GetIntConst (PowerOfTwo (opnd1. arg(D.Const). int),
                                      D.struct[D.strShortInt]))
          END
        END
        
      | Opc.classDivInt:
        IF (opnd2. arg IS D.Const) THEN
          (* a DIV const *)
          IF (opnd2. arg(D.Const). int = -1) THEN
            (* a DIV -1 ==> -a *)
            replacement := instr. region. CreateInstruction (Opc.baseNeg + subClass, instr. type, instr. pos);
            replacement(D.Instruction). Operand (opnd1. arg);
            EXCL (instr. flags, D.instrNotDead)
          ELSIF (PowerOfTwo (opnd2. arg(D.Const). int) >= 0) THEN
            (* replace division by power of two with an arithmetic shift *)
            replacement := instr. region. CreateInstruction (Opc.baseAsh + subClass, instr. type, instr. pos);
            replacement(D.Instruction). Operand (opnd1. arg);
            replacement(D.Instruction). Operand (D.GetIntConst (-PowerOfTwo (opnd2. arg(D.Const). int),
                                      D.struct[D.strShortInt]));
            EXCL (instr. flags, D.instrNotDead)
          END
        END;

      | Opc.classDivReal:
        IF (opnd2. arg IS D.Const) THEN
          (* a DIV const *)
          IF (opnd2. arg(D.Const). real = -1) THEN
            (* a DIV -1 ==> -a *)
            replacement := instr. region. CreateInstruction ((Opc. classNeg * Opc.sizeClass) + subClass, instr. type, instr. pos);
            replacement(D.Instruction). Operand (opnd1. arg);
            EXCL (instr. flags, D.instrNotDead)
          END;
        END;

      | Opc.classMod:  
        IF (opnd2. arg IS D.Const) THEN
          (* a MOD const *)
          IF (ABS(opnd2. arg(D.Const). int) = 1) THEN
            (* a MOD +-1 ==> 0 *)
            replacement := GetZero (instr. type);
            EXCL (instr. flags, D.instrNotDead)
          ELSIF (opnd2. arg(D.Const). int = 0) THEN
            (* error: Division by zero *)
          ELSIF (PowerOfTwo (opnd2. arg(D.Const). int) >= 0) THEN
            replacement := ReplaceMod (subClass, opnd1. arg,
                                       opnd2. arg(D.Const). int-1);
            EXCL (instr. flags, D.instrNotDead)
          END;
        END;
        
      | Opc.classDiff:
        IF (opnd1. arg = opnd2. arg) OR (opnd1. arg = GetZero (instr. type)) OR (opnd2. arg = GetOne (instr. type)) THEN
          (* a - a       ==> {}
             {} - a      ==> {}
             a - fullSet ==> {} *)
          replacement := GetZero (instr. type);
        ELSIF (opnd2. arg = GetZero (instr. type)) THEN
          (* a - {} == a *)
          replacement := opnd1. arg;
        ELSIF (opnd1. arg = GetOne (instr. type)) THEN
          replacement := instr. region. CreateInstruction ((Opc.classCompl * Opc.sizeClass) + subClass, instr. type, instr. pos);
          replacement(D.Instruction). Operand (opnd2. arg);
        END;
      | Opc.classSymDiff:
        IF (opnd1. arg = opnd2. arg) THEN
          (* a / a ==> {} *)
          replacement := GetZero (instr. type);
        ELSIF (opnd1. arg = GetZero (instr. type)) THEN
          (* {} / a == a *)
          replacement := opnd2. arg;
        ELSIF (opnd1. arg = GetOne (instr. type)) OR (opnd2. arg = GetOne (instr. type)) THEN
          (* fullSet / a == -a
             a / fullSet == -a *)
          replacement := instr. region. CreateInstruction ((Opc.classCompl * Opc.sizeClass) + subClass, instr. type, instr. pos);
          IF (opnd1. arg = GetOne (instr. type)) THEN
            replacement(D.Instruction). Operand (opnd2. arg);
          ELSE
            replacement(D.Instruction). Operand (opnd1. arg);
          END;
        END;
      | Opc.classUnion:
        IF (opnd1. arg = opnd2. arg) THEN
         (* a + a ==> a *)
          replacement := opnd1. arg;
        ELSIF (opnd2. arg = GetOne (instr. type)) OR (opnd1. arg = GetOne (instr. type)) THEN
          (* a + fullSet ==> fullSet
             fullset + a ==> fullSet *)
          replacement := GetOne (instr. type);
        END;
      | Opc.classInter:
        IF (opnd1. arg = opnd2. arg) THEN
         (* a * a ==> a *)
          replacement := opnd1. arg;
        END;
      | Opc.classCompl:
        IF (opnd1. arg IS D.Instruction) & ((opnd1. arg(D.Instruction). opcode DIV Opc.sizeClass) = Opc.classCompl) THEN
          (* --a == a *)
          replacement := opnd1. arg(D.Instruction). opndList. arg;
        END;
      ELSE
      END;
      RETURN replacement;
    END ArithmTransform;
  
  PROCEDURE HandleComparison (instr: D.Instruction): D.Usable;
    VAR
      replacement: D.Usable;
      const: D.Const;
      arg: D.Result;
      opnd: D.Opnd;
      class: INTEGER;
      upperBound, lowerBound: D.Const;
      rangeSubClass: SHORTINT;
      
    PROCEDURE Negation (opnd: D.Opnd): D.Usable;
      VAR
        instr: D.Instruction;
      BEGIN
        instr := opnd. instr. region. CreateInstruction (Opc.notsu, D.struct[D.strBoolean], opnd. pos);
        instr. Operand (opnd. arg);
        RETURN instr                              
      END Negation;
      
    PROCEDURE GetMinMax (type: SHORTINT; max: BOOLEAN): D.Const;
    (* Return minimum/maxmium value of `type' as LONGREAL constant.
       ATTENTION: This code does not work properly, if the number of
                  bits in LONGREAL's mantisa < number of bits or LONGINT! *)
      VAR
        res: D.Const;
      BEGIN
        res := NIL;
        IF max THEN
          CASE type OF
          | Opc.subclS .. Opc.subclLU : 
            res := D.GetRealConst(Types.WholeMax (type), D.struct[D.strLongReal]);
          | Opc.subclR : 
            res := D.GetRealConst(Types.maxReal, D.struct[D.strLongReal]);
          | Opc.subclD : 
            res := D.GetRealConst(Types.maxLongReal, D.struct[D.strLongReal]);
          END;
        ELSE
          CASE type OF        
          | Opc.subclS .. Opc.subclLU:
            res := D.GetRealConst(Types.WholeMin (type), D.struct[D.strLongReal]);
          | Opc.subclR : res := D.GetRealConst(Types.minReal, D.struct[D.strLongReal]);
          | Opc.subclD : res := D.GetRealConst(Types.minLongReal, D.struct[D.strLongReal]);
          END;
        END;
        RETURN res;
      END GetMinMax;
    
    PROCEDURE RangeFolding (class: INTEGER; const: LONGREAL; lowerBound, upperBound: LONGREAL): D.Usable;
      (* checks, if "`const' CMP `lower-/upperBound'" *)
      BEGIN
        IF ((class = Opc.classLss) & (const < lowerBound)) OR
          ((class = Opc.classLeq) & (const <= lowerBound)) OR
          ((class = Opc.classGtr) & (const > upperBound)) OR
          ((class = Opc.classGeq) & (const >= upperBound)) OR
          ((class = Opc.classNeq) & ((const < lowerBound) OR (const > upperBound))) THEN
          IF debug THEN O.String ("comparison always TRUE due to limited range"); O.Ln; END;
          RETURN Sym.constTrue;
        ELSIF ((class = Opc.classLss) & (const >= upperBound)) OR
          ((class = Opc.classLeq) & (const > upperBound)) OR
          ((class = Opc.classGtr) & (const <= lowerBound)) OR
          ((class = Opc.classGeq) & (const < lowerBound)) OR
          ((class = Opc.classEql) & ((const < lowerBound) & (const > upperBound))) THEN
          IF debug THEN O.String ("comparison always FALSE due to limited range"); O.Ln; END;
          RETURN Sym.constFalse;
        END;
        RETURN NIL;
      END RangeFolding;
    
    BEGIN
      replacement := NIL;
      
      IF (instr. opndList. arg IS D.Const) OR (instr. opndList. nextOpnd. arg IS D.Const) THEN
        (* extract constant and result operand *)
        class := instr. opcode DIV Opc.sizeClass;
        IF (instr. opndList. arg IS D.Const) THEN
          const :=  instr. opndList. arg(D.Const);
          IF (instr. opndList. nextOpnd. arg IS D.Result) THEN
            opnd := instr. opndList. nextOpnd; 
            arg := opnd. arg(D.Result);
          ELSE
            RETURN NIL;
          END
        ELSIF (instr. opndList. nextOpnd. arg IS D.Const) THEN
          const :=  instr. opndList. nextOpnd. arg(D.Const);
          IF (instr. opndList. arg IS D.Result) THEN
            opnd := instr. opndList;
            arg := opnd. arg(D.Result);
          ELSE
            RETURN NIL;
          END;
          CASE class OF
          | Opc.classLss: class := Opc.classGtr;
          | Opc.classLeq: class := Opc.classGeq;
          | Opc.classGtr: class := Opc.classLss;
          | Opc.classGeq: class := Opc.classLeq;
          ELSE
          END;
        ELSE
          RETURN NIL;
        END;
  
        (* form of comparison: "const RELOP result" *)
        
        IF (const. type. form = D.strBoolean) THEN
          (* here holds: (class = classEql) OR (class = classNeq) *)
          IF ((class = Opc.classEql) = (const = Sym.constTrue)) THEN
            RETURN arg;
          ELSE
            RETURN Negation (opnd);
          END;
        ELSE
          IF (arg IS D.Instruction) THEN
            IF ((arg(D.Instruction). opcode DIV Opc.sizeClass) = Opc.classConv) THEN          
            (* `oper' is result of a type conversion, so we can make some 
              assumptions about its range and check these boundaries against `const'. *)
              rangeSubClass := SHORT(SHORT(arg(D.Instruction). opndList. arg(D.Const). int));
              upperBound := GetMinMax (rangeSubClass, TRUE);
              lowerBound := GetMinMax (rangeSubClass, FALSE);
              IF Sym.TypeInGroup (const. type, D.grpReal) THEN
                replacement := RangeFolding (class, const. real, lowerBound. real, upperBound. real)
              ELSE
                replacement := RangeFolding (class, const. int, lowerBound. real, upperBound. real)
              END
            END;
          ELSE
            (* no instruction... *)
            (* special cases, e.g.: a < MAX(type[a])... *)
          END;
        END;
      ELSE (* both operands are not constant *)
        (* a <= b-1 == a < b
           a+1 >= b == a > b *)
(*        IF Sym.TypeInGroup (instr. opndList. arg. type, D.grpInteger) THEN
          IF (class = Opc.classLeq) THEN
            (* a <= x *)
            opnd1 := instr. opndList;
            opnd2 := opnd1. nextOpnd;
            IF (opnd2. arg IS D.Instruction) & 
               ((opnd2. arg(D.Instruction). opcode DIV Opc.sizeClass) = Opc.classSub) THEN
              (* a <= (y-z) *)
              subInstr := opnd2. arg(D.Instruction);
              IF (subInstr. opndList. nextOpnd. arg = GetOne (subInstr. type)) THEN
                (* a <= (y-1) *)
                replacement := D.CreateInstruction (instr. region, (Opc.classLss * Opc.sizeClass) + (subInstr.opcode MOD Opc.sizeClass), subInstr. type, instr. pos);
                D.Operand (replacement(D.Instruction), opnd1. arg);
                D.Operand (replacement(D.Instruction), subInstr. opndList. arg);
              END;
            END;
          ELSIF (class = Opc.classGeq) THEN
            (* x >= b *)
            opnd1 := instr. opndList;
            opnd2 := opnd1. nextOpnd;
            IF (opnd1. arg IS D.Instruction) &
               ((opnd1. arg(D.Instruction). opcode DIV Opc.sizeClass) = Opc.classSub) THEN
              (* (y-z) >= b *)
              subInstr := opnd1. arg(D.Instruction);
              IF (subInstr. opndList. nextOpnd. arg = GetOne (subInstr. type)) THEN
                (* (y-1) >= b == b < y *)
                replacement := D.CreateInstruction (instr. region, (Opc.classLss * Opc.sizeClass) + (subInstr.opcode MOD Opc.sizeClass), subInstr. type, instr. pos);
                D.Operand (replacement(D.Instruction), opnd2. arg);
                D.Operand (replacement(D.Instruction), subInstr. opndList. arg);
              END;
                
          END;
        END;
*)        
      END;
      RETURN replacement;
    END HandleComparison;

  BEGIN
    worklist.Init;
    InitialWorklist (reg);
    
    WHILE ~worklist.IsEmpty() DO
      (* fetch `instr' from `worklist' *)
      iInstr := worklist. GetHead ();
      worklist.RemoveHead;
      instr := iInstr(D.Instruction); 

      subClass := (instr. opcode MOD Opc.sizeClass);
      class := (instr. opcode DIV Opc.sizeClass);
      replacement := NIL;
      IF ((class = Opc.classEql) OR (class = Opc.classLeq) OR (class = Opc.classGeq))  & 
            (instr. opndList. arg = instr. opndList. nextOpnd. arg) THEN
        replacement := Sym.constTrue;
      ELSIF ((class = Opc.classNeq) OR (class = Opc.classLss) OR (class = Opc.classGtr)) & 
            (instr. opndList. arg = instr. opndList. nextOpnd. arg) THEN
        replacement := Sym.constFalse;
      ELSIF (Opc.classEql <= class) & (class <= Opc.classGeq) THEN
        replacement := HandleComparison (instr);   
      ELSIF (instr. type = D.struct[D.strBoolean]) THEN
        IF (instr. opcode >= Opc.baseConv) THEN
          replacement := BooleanResult (instr);
        END;
      ELSE
        replacement := RemoveNeutralOpnd (instr);
        IF (replacement = NIL) THEN
          replacement := ArithmTransform (instr);
        END;
      END;
      IF (replacement # NIL) THEN
        worklist.AddUsingInstr (instr, NIL);
        instr. ReplaceUses (replacement);
      END
    END; 
  END Transform;
  
END AlgebraicTransformation.
