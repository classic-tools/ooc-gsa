(*	$Id: CNIdentifier.Mod,v 1.3 1998/09/25 18:02:38 acken Exp $	*)
MODULE CNIdentifier;
(*  Scans all using occurences of names and connects them to their definitions.
    Copyright (C) 1998  Michael van Acken

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
  Out,
  S := CNScanner, AST := CNAST, SymTab := CNSymTab, Parser := CNParser;


(*

A module can be used in 
  o an IMPORT statement (which appear in the use list of the original module)
  o a qualified identifier (which appears in the use list of the import object)
  
A type is a type constructor or a type name.  It can appear as part of
  o a type constructor, or
  o a type, variable, field, or parameter declaration, or
  o a type test, type guard, or WITH statement, or
  o a procedure call (MIN, MAX, VAL).

A constant, variable, field, or procedure can be used
  o in an expression (l-value),  or
  o as a field selector (fields and tb procedures only), or
  o on the left side of an assignment (variables and fields only), or
  o in/out argument for a VAR parameter (variables and fields only), or
  o for a procedure or function call (procedure only).

*)


PROCEDURE NotFound (ident: AST.Ident);
  VAR
    start: S.Symbol;
  BEGIN
    start := ident. name;
    WHILE (start. prev # NIL) DO
      start := start. prev
    END;
    Out.String ("In file ");
    Out.String (start(S.StartSymbol). file^);
    Out.String (": ");
    Out.Ln;
    Out.LongInt (ident. name. pos, 0);
    Out.String (": Undeclared identifier");
    Out.Ln;
    HALT (1)
  END NotFound;

PROCEDURE TypeError (sym: AST.Symbol);
  VAR
    start: S.Symbol;
  BEGIN
    start := sym;
    WHILE (start. prev # NIL) DO
      start := start. prev
    END;
    Out.String ("In file ");
    Out.String (start(S.StartSymbol). file^);
    Out.String (": ");
    Out.Ln;
    Out.LongInt (sym. pos, 0);
    Out.String (": Type error");
    Out.Ln;
    HALT (1)
  END TypeError;


(*DEBUG
PROCEDURE WriteScope (scope: SymTab.Object);
  PROCEDURE WriteObj (obj: SymTab.Object);
    BEGIN
      IF (obj # NIL) THEN
        WriteObj (obj. leftObj);
        Out.String ("  ");
        Out.String (obj. name^);
        Out.Ln;
        WriteObj (obj. rightObj)
      END
    END WriteObj;
  
  BEGIN
    WHILE (scope # NIL) DO
      Out.String ("scope ");
      Out.String (scope.name^);
      Out.Ln;
      WriteObj (scope. localDecl);
      IF (scope. localTo # NIL) THEN
        IF (scope. localTo IS SymTab.Object) THEN
          scope := scope. localTo(SymTab.Object)
        ELSE
          scope := NIL;
          Out.String ("scope struct");
          Out.Ln
        END
      ELSE
        scope := NIL;
        Out.String ("scope NIL");
        Out.Ln;
      END
    END
  END WriteScope;*)


PROCEDURE Ident (ident: AST.Ident; scope: SymTab.Object);
  VAR
    obj: SymTab.Object;
  BEGIN
    obj := SymTab.Find (scope, ident. name. str^);
    IF (obj = NIL) THEN
      NotFound (ident)
    ELSE
      obj. AddUse (ident)
    END
  END Ident;

PROCEDURE Qualident (qident: AST.Qualident; scope: SymTab.Object);
  VAR
    obj: SymTab.Object;
  BEGIN
    IF (qident. module = NIL) THEN
      obj := SymTab.Find (scope, qident. ident. name. str^);
      IF (obj = NIL) THEN
        NotFound (qident. ident)
      ELSE
        obj. AddUse (qident. ident)
      END
    ELSE
      obj := SymTab.Find (scope, qident. module. name. str^);
      IF (obj = NIL) THEN
        NotFound (qident. module)
      ELSE
        obj. AddUse (qident. module)
      END;
      obj := SymTab.FindDecl (obj. localDecl, qident. ident. name. str^);
      IF (obj = NIL) THEN
        NotFound (qident. ident)
      ELSE
        obj. AddUse (qident. ident)
      END
    END
  END Qualident;

PROCEDURE ^ Expr (expr: AST.Expr; scope: SymTab.Object);

PROCEDURE ^ Type (type: AST.Type; scope: SymTab.Object);

PROCEDURE Designator (design: AST.Designator; scope: SymTab.Object): AST.TypeGuard;
  VAR
    fixCall: AST.TypeGuard;
    obj: SymTab.Object;
    type: SymTab.Struct;
    
  PROCEDURE Dim (t: SymTab.Struct): INTEGER;
    BEGIN
      IF (t.form # SymTab.strArray) & (t.form # SymTab.strOpenArray) THEN
        RETURN 0
      ELSE
        RETURN Dim(t.base)+1
      END
    END Dim;
  
  PROCEDURE Selector (VAR s: AST.Selector; type: SymTab.Struct;
                      tbProc: BOOLEAN);
    VAR
      expr: AST.Expr;
      obj: SymTab.Object;
    BEGIN
      IF (s # NIL) THEN
        WITH s: AST.Member DO
          IF (type. form = SymTab.strPointer) THEN
            type := SymTab.ResolveType (type. base)
          END;
          IF (type. form # SymTab.strRecord) THEN
            TypeError (s. FirstSym())
          END;
          
          obj := SymTab.FindDecl (type, s. name. name. str^);
          IF (obj = NIL) THEN
            NotFound (s. name)
          ELSE
            obj. AddUse (s. name)
          END;
          type := SymTab.ResolveType (obj. type);
          IF (obj. mode = SymTab.objTBProc) THEN
            tbProc := TRUE
          END

        | s: AST.Index DO
          IF (type. form = SymTab.strPointer) THEN
            type := SymTab.ResolveType (type. base)
          END;
          expr :=  s. exprList;
          WHILE (expr # NIL) DO
            IF (type. form # SymTab.strArray) & 
               (type. form # SymTab.strOpenArray) THEN
              TypeError (s. FirstSym())
            END;
            Expr (expr, scope);
            type := SymTab.ResolveType (type. base);
            expr := expr. next
          END

        | s: AST.Deref DO
          IF tbProc THEN
            IF (s. next # NIL) & ~(s. next IS AST.TypeGuard) THEN
              TypeError (s. arrow)
            END
          ELSE
            IF (type. form # SymTab.strPointer) THEN
              TypeError (s. arrow)
            ELSE
              type := SymTab.ResolveType (type. base)
            END
          END;

        | s: AST.TypeGuard DO
          ASSERT (s. type IS AST.TypeName);  (* or the parser is broken *)
          IF (type. form = SymTab.strProc) THEN
            (* we parsed a procedure call as a type guard; now we must clean
               up this mess and rebuild the syntax tree to reflect the true
               nature of things *)
            IF (design. up IS AST.Assignment) THEN
              TypeError (s. lParen)
            ELSE (* designator is part of `FactorDesign' or `ProcCall' *)
              fixCall := s;
              s := NIL
            END
          ELSE
            Type (s. type, scope);
            IF (type. form # SymTab.strRecord) &
               ((type. form # SymTab.strPointer) OR 
                (type. base. form # SymTab.strRecord)) OR
               ~(s. type IS AST.TypeName) THEN
              TypeError (s. lParen)
            END;
            obj := s. type(AST.TypeName). qualident. ident. obj(SymTab.Object);
            IF (obj. mode # SymTab.objType) THEN
              TypeError (s. lParen)
            END;
            type := SymTab.ResolveType (obj. type)
          END
        END;
        IF (s # NIL) THEN  (* FALSE if a type guard must be rewritten *)
          Selector (s. next, type, tbProc)
        END
      END
    END Selector;
  
  PROCEDURE AdjustForWith (node: AST.Node; oldType: SymTab.Struct): SymTab.Struct;
    VAR
      id0, id1: AST.Ident;
    BEGIN
      id0 := design. qualident. ident;
      WHILE ~(node IS AST.Body) DO
        WITH node: AST.WithBranch DO
          id1 := node. var. ident;
          IF (id0. obj = id1. obj) THEN
            (* some qualified identifier: get type from WITH statement *)
            RETURN SymTab.ResolveType (node. type(AST.TypeName). qualident. 
                                       ident. obj(SymTab.Object). type)
          END
        ELSE (* ignore *)
        END;
        node := node. up
      END;
      RETURN oldType
    END AdjustForWith;
  
  BEGIN
    Qualident (design. qualident, scope);
    fixCall := NIL;
    obj := design. qualident. ident. obj(SymTab.Object);
    type := SymTab.ResolveType (obj. type);
    
    IF (scope. info = scope) THEN
       (* qualident is part of a WITH; searching through the surrounding
          statements for a matching WITH might not be the peak of elegance,
          but it will do *)
      type := AdjustForWith (design. up, type)
    END;
    
    Selector (design. selectors, type, FALSE);
    RETURN fixCall
  END Designator;

PROCEDURE ExprList (exprList: AST.ExprList; scope: SymTab.Object);
  VAR
    expr: AST.Expr;
  BEGIN
    expr := exprList;
    WHILE (expr # NIL) DO
      Expr (expr, scope);
      expr := expr. next
    END
  END ExprList;

PROCEDURE MoveSymbol (sym: AST.Symbol; toUp: AST.Node; VAR to: AST.Symbol);
  BEGIN
    sym. up := toUp;
    to := sym
  END MoveSymbol;

PROCEDURE QualidentToExpr (qident: AST.Qualident; toUp: AST.Node; 
                           VAR to: AST.Expr);
  VAR
    design: AST.Designator;
    fctCall: AST.FctCall;
  BEGIN
    NEW (design);
    design. up := NIL;
    design. qualident := qident; qident. up := design;
    design. selectors := NIL;
    
    NEW (fctCall);
    Parser.InitExpr (fctCall, toUp, NIL);
    fctCall. design := design; design. up := fctCall;
    fctCall. lParen := NIL;
    fctCall. arguments := NIL;
    fctCall. rParen := NIL;
    
    to := fctCall
  END QualidentToExpr;

PROCEDURE Expr (expr: AST.Expr; scope: SymTab.Object);
  PROCEDURE Factor (f: AST.Factor; scope: SymTab.Object);
    VAR
      elem: AST.SetElement;
      fixCall: AST.TypeGuard;
    BEGIN
      WITH f: AST.FctCall DO
        fixCall := Designator (f. design, scope);
        IF (fixCall # NIL) THEN
          IF (f. lParen # NIL) THEN
            TypeError (f. lParen)
          END;
          MoveSymbol (fixCall. lParen, f, f. lParen);
          MoveSymbol (fixCall. rParen, f, f. rParen);
          QualidentToExpr (fixCall. type(AST.TypeName). qualident,
                           f, f. arguments)
        END;
        ExprList (f. arguments, scope)
        
      | f: AST.Literal DO
      
      | f: AST.FactorExpr DO
        Expr (f. expr, scope)
      
      | f: AST.Set DO
        elem := f. elements;
        WHILE (elem # NIL) DO
          IF (elem. lower # NIL) THEN
            Expr (elem. lower, scope)
          END;
          IF (elem. upper # NIL) THEN
            Expr (elem. upper, scope)
          END;
          elem := elem. next
        END
      END
    END Factor;
  
  BEGIN
    WITH expr: AST.Operator DO
      IF (expr. left # NIL) THEN
        Expr (expr. left, scope)
      END;
      Expr (expr. right, scope)
      
    | expr: AST.Factor DO
      Factor (expr, scope)
    END
  END Expr;

PROCEDURE FormalPars (fpar: AST.FormalPars; scope: SymTab.Object);
  VAR
    decl: AST.Decl;
  BEGIN
    decl := fpar. fpSections;
    WHILE (decl # NIL) DO
      IF (decl(AST.FPSection). type # NIL) THEN  (* not "three dots" *)
        Type (decl(AST.FPSection). type, scope)
      END;
      decl := decl. next
    END;
    IF (fpar. resultType # NIL) THEN
      Type (fpar. resultType, scope)
    END
  END FormalPars;

PROCEDURE Type (type: AST.Type; scope: SymTab.Object);
  VAR
    decl: AST.Decl;
  BEGIN
    WITH type: AST.TypeName DO
      Qualident (type. qualident, scope)
    | type: AST.Array DO
      ExprList (type. exprList, scope);
      Type (type. type, scope)
    | type: AST.Record DO
      IF (type. base # NIL) THEN
        Type (type. base, scope)
      END;
      decl := type. fields;
      WHILE (decl # NIL) DO
        IF (decl(AST.FieldList). type # NIL) THEN
          Type (decl(AST.FieldList). type, scope)
        END;
        decl := decl. next
      END
    | type: AST.Pointer DO
      Type (type. base, scope)
    | type: AST.ProcType DO
      FormalPars (type. fpars, scope)
    END
  END Type;


PROCEDURE StatmSeq (statmSeq: AST.StatmSeq; scope: SymTab.Object);
  VAR
    statm: AST.Statement;
    elsif: AST.Elsif;
    caseBranch: AST.CaseBranch;
    label: AST.CaseLabels;
    withBranch: AST.WithBranch;
    fixCall: AST.TypeGuard;
    oldInfo: S.Info;
  BEGIN
    statm := statmSeq;
    WHILE (statm # NIL) DO
      WITH statm: AST.Assignment DO
        fixCall := Designator (statm. dest, scope);
        ASSERT (fixCall = NIL);
        Expr (statm. value, scope)
        
      | statm: AST.ProcCall DO
        fixCall := Designator (statm. proc, scope);
        IF (fixCall # NIL) THEN
          IF (statm. lParen # NIL) THEN
            TypeError (statm. lParen)
          END;
          MoveSymbol (fixCall. lParen, statm, statm. lParen);
          MoveSymbol (fixCall. rParen, statm, statm. rParen);
          QualidentToExpr (fixCall. type(AST.TypeName). qualident,
                           statm, statm. arguments)
        END;
        ExprList (statm. arguments, scope)
        
      | statm: AST.If DO
        Expr (statm. guard, scope);
        StatmSeq (statm. statmSeq, scope);
        elsif := statm. elsifList;
        WHILE (elsif # NIL) DO
          Expr (elsif. guard, scope);
          StatmSeq (elsif. statmSeq, scope);
          elsif := elsif. next
        END;
        StatmSeq (statm. elseStatm, scope)
        
      | statm: AST.Case DO
        Expr (statm. selector, scope);
        caseBranch := statm. branches;
        WHILE (caseBranch # NIL) DO
          label := caseBranch. labels;
          WHILE (label # NIL) DO
            Expr (label. lower, scope);
            IF (label. upper # NIL) THEN
              Expr (label. upper, scope)
            END;
            label := label. next
          END;
          StatmSeq (caseBranch. statmSeq, scope);
          caseBranch := caseBranch. next
        END;
        StatmSeq (statm. elseStatm, scope)
        
      | statm: AST.While DO
        Expr (statm. guard, scope);
        StatmSeq (statm. statmSeq, scope)
        
      | statm: AST.Repeat DO
        StatmSeq (statm. statmSeq, scope);
        Expr (statm. guard, scope)
        
      | statm: AST.For DO
        Ident (statm. var, scope);
        Expr (statm. lower, scope);
        Expr (statm. upper, scope);
        IF (statm. step # NIL) THEN
          Expr (statm. step, scope)
        END;
        StatmSeq (statm. statmSeq, scope)
        
      | statm: AST.Loop DO
        StatmSeq (statm. statmSeq, scope)
        
      | statm: AST.With DO
        withBranch := statm. branches;
        WHILE (withBranch # NIL) DO
          Qualident (withBranch. var, scope);
          Type (withBranch. type, scope);
          oldInfo := scope. info;
          scope. info := scope;  (* mark scope as being modified by a WITH *)
          StatmSeq (withBranch. statmSeq, scope);
          scope. info := oldInfo;
          withBranch := withBranch. next
        END;
        StatmSeq (statm. elseStatm, scope)
        
      | statm: AST.Return DO
        IF (statm. value # NIL) THEN
          Expr (statm. value, scope)
        END
        
      ELSE (* EXIT or empty statement *)
      END;
      statm := statm. next
    END
  END StatmSeq;

PROCEDURE Body (body: AST.Body; scope: SymTab.Object);
  VAR
    decl: AST.Decl;  
  BEGIN
    decl := body. declSeq;
    WHILE (decl # NIL) DO
      IF (decl. name # NIL) THEN
        WITH decl: AST.ConstDecl DO
          Expr (decl. value, scope)
        | decl: AST.TypeDecl DO
          Type (decl. type, scope)
        | decl: AST.VarDecl DO
          Type (decl. type, scope)
        | decl: AST.ProcDecl DO
          IF (decl. receiver # NIL) THEN
            FormalPars (decl. receiver, scope)
          END;
          FormalPars (decl. fpars, scope);
          IF (decl. body # NIL) THEN
            Body (decl. body, decl. name. obj(SymTab.Object))
          END
        END
      END;
      decl := decl. next
    END;
    StatmSeq (body. statmSeq, scope)
  END Body;

PROCEDURE Module (module: AST.Module; imports: SymTab.Object);
  VAR
    decl: AST.Decl;
  
  PROCEDURE Import (import: AST.Import);
    VAR
      symTab: SymTab.Object;
      mname: AST.Ident;
    BEGIN
      (* locate imported module *)
      mname := import. module;
      IF (mname. name. str^ = "SYSTEM") THEN
        symTab := SymTab.system
      ELSE
        symTab := imports;
        WHILE (symTab. name^ # mname. name. str^) DO
          symTab := symTab. rightObj
        END
      END;
      symTab. AddUse (import. module)
    END Import;
  
  BEGIN
    IF (module. importList # NIL) THEN
      decl := module. importList. imports;
      WHILE (decl # NIL) DO
        Import (decl(AST.Import));
        decl := decl. next
      END
    END;
    IF (module. body # NIL) THEN
      Body (module. body, module. name. obj(SymTab.Object))
    END
  END Module;


PROCEDURE CreateUseLists* (module: AST.Module; imports: SymTab.Object);
(* pre: SymTab.CreateSymTab has been run successfully on `module' *)
  BEGIN
    Module (module, imports);
    
  END CreateUseLists;


END CNIdentifier.
