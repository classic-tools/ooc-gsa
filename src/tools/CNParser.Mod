(*	$Id: CNParser.Mod,v 1.12 1999/11/22 22:57:16 ooc-devel Exp $	*)
MODULE CNParser;
(*  Creates an abstract syntax tree from an Oberon-2 module.
    Copyright (C) 1998, 1999  Michael van Acken

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
  Out, Strings, S := CNScanner, AST := CNAST, Decl := CNDecl;


VAR
  sym: S.Symbol;                         (* current symbol in input stream *)
  import: AST.Import;                    (* import list of current module *)
  interface: BOOLEAN;                    (* TRUE for interface modules *)


(*PROCEDURE WriteStack (node: AST.Node);
  VAR
    type: Types.Type;
  BEGIN
    Out.String ("Stack: ");
    Out.Ln;
    WHILE (node # NIL) DO
      type := Types.TypeOf (node);
      Out.String ("  ");
      Out.String (type. name^);
      Out.Ln;
      node := node. up
    END
  END WriteStack;*)

PROCEDURE SynErr (node: AST.Node);
(* Signals a syntax error at the position of the given symbol, then aborts
   program.  *)
  VAR
    start: S.Symbol;
  BEGIN
    start := sym;
    IF (start # NIL) THEN
      WHILE (start. prev # NIL) DO
        start := start. prev
      END;
      Out.String ("In file ");
      Out.String (start(S.StartSymbol). file^);
      Out.String (": ");
      Out.Ln;
      Out.LongInt (sym. pos, 0);
      Out.String (": Syntax error");
      Out.Ln;
      HALT (1)
    ELSE
      Out.String ("Error: Input file is empty");
      Out.Ln;
      HALT (1)
    END
  END SynErr;

PROCEDURE GetSym (up: AST.Node): AST.Symbol;
  VAR
    symbol: AST.Symbol;
  BEGIN
(*Out.String ("passed: "); Out.String (sym. str^); 
Out.String ("  ("); Out.LongInt (sym. line, 0); Out.String (", ");
Out.LongInt (sym. column, 0); Out.String (")"); Out.Ln;*)
    symbol := sym;
    symbol. up := up;
    sym := sym. next;
    WHILE (sym # NIL) & (sym. id >= S.comment) DO
      sym := sym. next
    END;
    RETURN symbol
  END GetSym;

PROCEDURE CheckSym (up: AST.Node; symId: SHORTINT): AST.Symbol;
  BEGIN
    IF (sym. id = symId) THEN
      RETURN GetSym (up)
    ELSE
(*Out.String ("expected: "); Out.Int (symId, 0); Out.Ln;
Out.String ("got: "); Out.Int (sym. id, 0); Out.Ln;*)
      SynErr (up); RETURN NIL
    END
  END CheckSym;

PROCEDURE Flags (up: AST.Node): AST.FlagList;
  VAR
    flagList: AST.FlagList;
  BEGIN
    IF (sym. id = S.lBrak) THEN
      NEW (flagList);
      flagList. up := up;
      flagList. first := sym;
      WHILE (sym # NIL) & (sym. id # S.rBrak) DO
        sym. up := flagList;
        sym := sym. next
      END;
      flagList. last := sym;
      IF (sym # NIL) THEN
        sym. up := flagList;
        REPEAT
          sym := sym.  next
        UNTIL (sym = NIL) OR (sym. id < S.comment)
      END;
      RETURN flagList
    ELSE
      RETURN NIL
    END
  END Flags;

PROCEDURE FlagIsPresent (flags: AST.FlagList; name: ARRAY OF CHAR): BOOLEAN;
  VAR
    flag: AST.Symbol;
  BEGIN
    IF (flags # NIL) THEN
      flag := flags. first;
      WHILE (flag # NIL) DO
        IF (flag. id = S.ident) & (flag. str^ = name) THEN
          RETURN TRUE
        END;
        flag := flag. next
      END
    END;
    RETURN FALSE
  END FlagIsPresent;

PROCEDURE Ident (up: AST.Node): AST.Ident;
  VAR
    ident: AST.Ident;
  BEGIN
    NEW (ident);
    ident. up := up;
    ident. name := CheckSym (ident, S.ident);
    ident. obj := NIL;
    ident. nextUse := NIL;
    RETURN ident
  END Ident;

PROCEDURE IdentDef (up: AST.Node; parseFlags: BOOLEAN): AST.IdentDef;
  VAR
    ident: AST.IdentDef;
  BEGIN
    NEW (ident);
    ident. up := up;
    ident. name := CheckSym (ident, S.ident);
    
    IF (sym. id = S.times) THEN
      ident. mark := GetSym (ident)
    ELSIF (sym. id= S.minus) THEN
      ident. mark := GetSym (ident)
    ELSE
      ident. mark := NIL
    END;
    IF parseFlags THEN
      ident. flags := Flags (ident)
    ELSE
      ident. flags := NIL
    END;
    
    ident. comma := NIL;
    ident. next := NIL;
    ident. prev := NIL;
    ident. obj := NIL;
    ident. nextUse := NIL;
    ident. info := NIL;
    RETURN ident
  END IdentDef;

PROCEDURE IdentList (up: AST.Node): AST.IdentDefList;
  VAR
    ident, first, last: AST.IdentDef;
  BEGIN  (* pre: (sym. id = S.ident) *)
    first := IdentDef (up, TRUE);
    last := first;
    WHILE (sym. id = S.comma) DO
      last. comma := GetSym (last);
      ident := IdentDef (up, TRUE);
      ident. prev := last;
      last. next := ident;
      last := ident
    END;
    RETURN first
  END IdentList;

PROCEDURE Qualident (up: AST.Node): AST.Qualident;
  VAR
    ident: AST.Ident;
    qident: AST.Qualident;
  BEGIN
    NEW (qident);
    qident. up := up;
    
    ident := Ident (qident);
    IF Decl.IsModuleName (up, ident. name) THEN
      qident. module := ident;
      qident. period := CheckSym (qident, S.period);
      qident. ident := Ident (qident)
    ELSE
      qident. module := NIL;
      qident. period := NIL;
      qident. ident := ident
    END;
    
    RETURN qident;
  END Qualident;



PROCEDURE ^ Expr (up: AST.Node): AST.Expr;
PROCEDURE ^ Type (up: AST.Node): AST.Type;


PROCEDURE ExprList (up: AST.Node): AST.ExprList;
  VAR
    expr, first, last: AST.Expr;
  BEGIN
    first := Expr (up);
    last := first;
    WHILE (sym. id = S.comma) DO
      last. comma := GetSym (last);
      expr := Expr (up);
      expr. prev := last;
      last. next := expr;
      last := expr
    END;
    RETURN first
  END ExprList;

PROCEDURE Designator (up: AST.Node): AST.Designator;
  VAR
    design: AST.Designator;
    selector, last: AST.Selector;
    member: AST.Member;
    index: AST.Index;
    deref: AST.Deref;
    typeGuard: AST.TypeGuard;
  
  PROCEDURE IsCall (sym: S.Symbol): BOOLEAN;
  (* Return TRUE if the symbol sequence starting with `sym' can't be a type
     guard.  
     pre: `sym' is a left parenthesis *)
    BEGIN
      sym := sym. next;
      IF (sym. id = S.ident) THEN
        IF Decl.IsModuleName (design, sym) THEN
          IF (sym. next. id # S.period) OR
             (sym. next. next. id # S.ident) THEN
            RETURN TRUE
          ELSE
            sym := sym. next. next
          END
        END;
        sym := sym. next;
        RETURN (sym. id # S.rParen)
      ELSE
        RETURN TRUE
      END
    END IsCall;
  
  BEGIN  (* pre: (sym. id = S.ident) *)
    NEW (design);
    design. up := up;
    design. qualident := Qualident (design);
    design. selectors := NIL;
    LOOP
      IF (sym. id = S.period) THEN
        NEW (member);
        member. up := design;
        member. period := GetSym (member);
        member. name := Ident (member);
        selector := member
        
      ELSIF (sym. id = S.lBrak) THEN
        NEW (index);
        index. up := design;
        index. lBrak := GetSym (index);
        index. exprList := ExprList (index);
        index. rBrak := CheckSym (index, S.rBrak);
        selector := index
        
      ELSIF (sym. id = S.arrow) THEN
        NEW (deref);
        deref. up := design;
        deref. arrow := GetSym (deref);
        selector := deref
        
      ELSIF (sym. id = S.lParen) & ~IsCall (sym) THEN
        NEW (typeGuard);
        typeGuard. up := design;
        typeGuard. lParen := GetSym (typeGuard);
        typeGuard. type := Type (typeGuard);
        typeGuard. rParen := CheckSym (typeGuard, S.rParen);
        selector := typeGuard
        
      ELSE
        EXIT
      END;
      
      IF (design. selectors = NIL) THEN
        selector. prev := NIL;
        selector. next := NIL;
        design. selectors := selector
      ELSE
        selector. prev := last;
        selector. next := NIL;
        last. next := selector
      END;
      last := selector
    END;
    RETURN design
  END Designator;

PROCEDURE InitExpr* (expr: AST.Expr; up: AST.Node; left: AST.Expr);
  BEGIN
    expr. up := up;
    expr. comma := NIL;
    expr. next := NIL;
    expr. prev := NIL;
    WITH expr: AST.Operator DO
      expr. left := left;
      IF (left # NIL) THEN left. up := expr END
    ELSE
    END
  END InitExpr;

PROCEDURE Expr (up: AST.Node): AST.Expr;
  VAR
    left: AST.Expr;
    expr: AST.Operator;
    
  PROCEDURE SimpleExpr (up: AST.Node): AST.Expr;
    VAR
      left: AST.Expr;
      expr: AST.Operator;

    PROCEDURE Term (up: AST.Node): AST.Expr;
      VAR
        left: AST.Expr;
        expr: AST.Operator;

      PROCEDURE Factor (up: AST.Node): AST.Expr;
        VAR
          fctCall: AST.FctCall;
          literal: AST.Literal;
          factorExpr: AST.FactorExpr;
          notOp: AST.Operator;
          
        PROCEDURE Set (up: AST.Node; qualident: AST.Qualident): AST.Set;
          VAR
            set: AST.Set;
            element, last: AST.SetElement;
            
          PROCEDURE Element (up: AST.Set): AST.SetElement;
            VAR
              elem: AST.SetElement;
            BEGIN
              NEW (elem);
              elem. up := up;
              elem. lower := Expr (elem);
              IF (sym. id = S.upto) THEN
                elem. upto := GetSym (elem);
                elem. upper := Expr (elem)
              ELSE
                elem. upto := NIL;
                elem. upper := NIL
              END;
              elem. next := NIL;
              elem. prev := NIL;
              RETURN elem
            END Element;

          BEGIN  (* pre: (sym. id = S.lBrace) *)
            NEW (set);
            InitExpr (set, up, NIL);
            
            IF (qualident # NIL) THEN
              qualident. up := set
            END;
            set. qualident := qualident;
            
            set. lBrace := GetSym (set);
            IF (sym. id # S.rBrace) THEN
              set. elements := Element(set);
              last := set. elements;
              WHILE (sym. id = S.comma) DO
                last. comma := GetSym (last);
                element := Element (set);
                element. prev := last;
                last. next := element;
                last := element
              END
            ELSE
              set. elements := NIL
            END;
            set. rBrace := CheckSym (set, S.rBrace);
            RETURN set
          END Set;

        BEGIN
          IF (sym. id = S.ident) THEN
            NEW (fctCall);
            InitExpr (fctCall, up, NIL);
            fctCall. design := Designator (fctCall);
            IF (sym. id = S.lParen) THEN
              fctCall. lParen := GetSym (fctCall);
              IF (sym. id = S.rParen) THEN
                fctCall. arguments := NIL
              ELSE
                fctCall. arguments := ExprList (fctCall)
              END;
              fctCall. rParen := CheckSym(fctCall, S.rParen);
            ELSIF (sym. id = S.lBrace) THEN
              (* type qualified set constructor; only valid if introduced by
                 a type name; emit syntax error if the designator had any 
                 selectors *)
              IF (fctCall. design. selectors # NIL) THEN
                SynErr (sym); RETURN NIL
              ELSE
                RETURN Set (up, fctCall. design. qualident)
              END
            ELSE
              (* we keep this a `FctCall' because we may find out later 
                 (in `CNIdentifier.Expr.Factor) that the designator includes
                 a type guard that is in fact a function call; to make
                 rebuilding of the syntax tree easier, it is simpler to 
                 leave a pseudo function call at this place *)
              fctCall. lParen := NIL;
              fctCall. arguments := NIL;
              fctCall. rParen := NIL
            END;
            RETURN fctCall
            
          ELSIF (sym. id = S.number) OR (*(sym. id = S.character) OR*)
                (sym. id = S.string) OR (sym. id = S.nil) THEN
            NEW (literal);
            InitExpr (literal, up, NIL);
            literal. literal := GetSym (literal);
            RETURN literal
            
          ELSIF (sym. id = S.lBrace) THEN
            RETURN Set (up, NIL)
            
          ELSIF (sym. id = S.lParen) THEN
            NEW (factorExpr);
            InitExpr (factorExpr, up, NIL);
            factorExpr. lParen := GetSym (factorExpr);
            factorExpr. expr := Expr (factorExpr);
            factorExpr. rParen := CheckSym(factorExpr, S.rParen);
            RETURN factorExpr
            
          ELSIF (sym. id = S.not) THEN
            NEW (notOp);
            InitExpr (notOp, up, NIL);
            notOp. op := GetSym (notOp);
            notOp. right := Factor (notOp);
            RETURN notOp
            
          ELSE
            SynErr (up);
            RETURN NIL
          END
        END Factor;

      BEGIN
        left := Factor (up);
        WHILE (S.times <= sym. id) & (sym. id <= S.and) DO
          NEW (expr);
          InitExpr (expr, up, left);
          expr. op := GetSym (expr);
          expr. right := Factor (expr);
          left := expr
        END;
        RETURN left
      END Term;

    BEGIN
      IF (sym. id = S.plus) OR (sym. id = S.minus) THEN
        NEW (expr);
        InitExpr (expr, up, NIL);
        expr. op := GetSym (expr);
        expr. right := Term (expr);
        left := expr
      ELSE
        left := Term (up)
      END;
      WHILE (S.plus <= sym. id) & (sym. id <= S.or) DO
        NEW (expr);
        InitExpr (expr, up, left);
        expr. op := GetSym (expr);
        expr. right := Term (expr);
        left := expr
      END;
      RETURN left
    END SimpleExpr;

  BEGIN
    left := SimpleExpr (up);
    IF (S.eql <= sym. id) & (sym. id <= S.is) THEN
      NEW (expr);
      InitExpr (expr, up, left);
      expr. op := GetSym (expr);
      expr. right := SimpleExpr (expr);
      RETURN expr
    ELSE
      RETURN left
    END
  END Expr;


PROCEDURE StatementSeq (up: AST.Node): AST.StatmSeq;
  VAR
    first, last, statm: AST.Statement;
    empty: BOOLEAN;
    
  PROCEDURE Statement (up: AST.Node; VAR empty: BOOLEAN): AST.Statement;
    VAR
      design: AST.Designator;
      assignment: AST.Assignment;
      procCall: AST.ProcCall;
      if: AST.If; elsif, lastElsif: AST.Elsif;
      case: AST.Case; lastCaseBranch, caseBranch: AST.CaseBranch;
      while: AST.While;
      repeat: AST.Repeat;
      for: AST.For;
      loop: AST.Loop;
      with: AST.With; lastWithBranch, withBranch: AST.WithBranch;
      exit: AST.Exit;
      return: AST.Return;
      
    PROCEDURE CaseBranch (up: AST.Case): AST.CaseBranch;
      VAR
        branch: AST.CaseBranch;
        labels, last: AST.CaseLabels;
        
      PROCEDURE CaseLabels (up: AST.CaseBranch): AST.CaseLabels;
        VAR
          labels: AST.CaseLabels;
        BEGIN
          NEW (labels);
          labels. up := up;
          labels. lower := Expr (labels);
          IF (sym. id = S.upto) THEN
            labels. upto := GetSym (labels);
            labels. upper := Expr (labels)
          ELSE
            labels. upto := NIL;
            labels. upper := NIL
          END;
          labels. comma := NIL;
          labels. next := NIL;
          labels. prev := NIL;
          RETURN labels
        END CaseLabels;

      BEGIN
        NEW (branch);
        branch. up := up;
        IF (sym. id < S.bar) THEN
          branch. labels := CaseLabels (branch);
          last := branch. labels;
          WHILE (sym. id = S.comma) DO
            last. comma := GetSym (last);
            labels := CaseLabels (branch);
            labels. prev := last;
            last. next := labels;
            last := labels
          END;
          branch. colon := CheckSym(branch, S.colon);
          branch. statmSeq := StatementSeq (branch)
        ELSE
          branch. labels := NIL;
          branch. colon := NIL;
          branch. statmSeq := NIL;
        END;
        branch. bar := NIL;
        branch. next := NIL;
        branch. prev := NIL;
        RETURN branch
      END CaseBranch;

    PROCEDURE WithBranch (up: AST.With; withKW: BOOLEAN): AST.WithBranch;
      VAR
        branch: AST.WithBranch;
      BEGIN
        NEW (branch);
        branch. up := up;
        IF withKW THEN
          branch. sep := CheckSym (branch, S.with)
        ELSE
          branch. sep := CheckSym (branch, S.bar)
        END;
        branch. var := Qualident (branch);
        branch. colon := CheckSym (branch, S.colon);
        IF (sym. id # S.ident) THEN  (* type name required *)
          SynErr (sym)
        END;
        branch. type := Type (branch);
        branch. do := CheckSym (branch, S.do);
        branch. statmSeq := StatementSeq (branch);
        branch. next := NIL;
        branch. prev := NIL;
        RETURN branch
      END WithBranch;
    
    PROCEDURE Init (statm: AST.Statement);
      BEGIN
        statm. Clear;
        statm. up := up
      END Init;
    
    BEGIN
      empty := FALSE;
      IF (sym. id = S.ident) THEN
        design := Designator (up);
        IF (sym. id = S.becomes) THEN
          NEW (assignment);
          Init (assignment);
          design. up := assignment;
          assignment. dest := design;
          assignment. becomes := GetSym (assignment);
          assignment. value := Expr (assignment);
          RETURN assignment
        ELSE
          NEW (procCall);
          Init (procCall);
          design. up := procCall;
          procCall. proc := design;
          IF (sym. id = S.lParen) THEN
            procCall. lParen := GetSym (procCall);
            IF (sym. id # S.rParen) THEN
              procCall. arguments := ExprList (procCall)
            ELSE
              procCall. arguments := NIL
            END;
            procCall. rParen := CheckSym (procCall, S.rParen)
          ELSE
            procCall. lParen := NIL;
            procCall. arguments := NIL;
            procCall. rParen := NIL
          END;
          RETURN procCall
        END
        
      ELSIF (sym. id = S.if) THEN
        NEW (if);
        Init (if);
        if. if := GetSym (if);
        if. guard := Expr (if);
        if. then := CheckSym (if, S.then);
        if. statmSeq := StatementSeq (if);
        
        if. elsifList := NIL;
        lastElsif := NIL;
        WHILE (sym. id = S.elsif) DO
          NEW (elsif);
          elsif. up := if;
          elsif. elsif := GetSym (elsif);
          elsif. guard := Expr (elsif);
          elsif. then := CheckSym (elsif, S.then);
          elsif. statmSeq := StatementSeq (elsif);
          IF (lastElsif = NIL) THEN
            elsif. prev := NIL;
            if. elsifList := elsif
          ELSE
            elsif. prev := lastElsif;
            lastElsif. next := elsif
          END;
          elsif. next := NIL;
          lastElsif := elsif
        END;
        
        IF (sym. id = S.else) THEN
          if. else := GetSym (if);
          if. elseStatm := StatementSeq (if)
        ELSE
          if. else := NIL;
          if. elseStatm := NIL
        END;
        if. end := CheckSym (if, S.end);
        RETURN if
        
      ELSIF (sym. id = S.case) THEN
        NEW (case);
        Init (case);
        case. case := GetSym (case);
        case. selector := Expr (case);
        case. of := CheckSym(case, S.of);
        
        case. branches := CaseBranch (case);
        lastCaseBranch := case. branches;
        WHILE (sym. id = S.bar) DO
          lastCaseBranch. bar := GetSym (lastCaseBranch);
          caseBranch := CaseBranch (case);
          caseBranch. prev := lastCaseBranch;
          lastCaseBranch. next := caseBranch;
          lastCaseBranch := caseBranch
        END;
        
        IF (sym. id = S.else) THEN
          case. else := GetSym (case);
          case. elseStatm := StatementSeq (case)
        ELSE
          case. else := NIL;
          case. elseStatm := NIL
        END;
        case. end := CheckSym(case, S.end);
        RETURN case
        
      ELSIF (sym. id = S.while) THEN
        NEW (while);
        Init (while);
        while. while := GetSym (while);
        while. guard := Expr (while);
        while. do := CheckSym (while, S.do);
        while. statmSeq := StatementSeq (while);
        while. end := CheckSym(while, S.end);
        RETURN while
        
      ELSIF (sym. id = S.repeat) THEN
        NEW (repeat);
        Init (repeat);
        repeat. repeat := GetSym (repeat);
        repeat. statmSeq := StatementSeq (repeat);
        repeat. until := CheckSym (repeat, S.until);
        repeat. guard := Expr (repeat);
        RETURN repeat
        
      ELSIF (sym. id = S.for) THEN
        NEW (for);
        Init (for);
        for. for := GetSym (for);
        for. var := Ident (for);
        for. becomes := CheckSym (for, S.becomes);
        for. lower := Expr (for);
        for. to := CheckSym (for, S.to);
        for. upper := Expr (for);
        IF (sym. id = S.by) THEN
          for. by := GetSym (for);
          for. step := Expr (for)
        ELSE
          for. by := NIL;
          for. step := NIL
        END;
        for. do := CheckSym (for, S.do);
        for. statmSeq := StatementSeq (for);
        for. end := CheckSym (for, S.end);
        RETURN for
        
      ELSIF (sym. id = S.loop) THEN
        NEW (loop);
        Init (loop);
        loop. loop := GetSym (loop);
        loop. statmSeq := StatementSeq (loop);
        loop. end := CheckSym (loop, S.end);
        RETURN loop
        
      ELSIF (sym. id = S.with) THEN
        NEW (with);
        Init (with);
        withBranch := WithBranch (with, TRUE);
        with. branches := withBranch;
        lastWithBranch := withBranch;
        WHILE (sym. id = S.bar) DO
          withBranch := WithBranch (with, FALSE);
          withBranch. prev := lastWithBranch;
          lastWithBranch. next := withBranch;
          lastWithBranch := withBranch
        END;
        
        IF (lastWithBranch. colon = NIL) & (lastWithBranch. sep = NIL) THEN
          (* the last branch is completely empty; this confuses navigation
             through the tree using Next()/Prev(), so we better discard it *)
          lastWithBranch. prev. next := NIL;
          lastWithBranch. prev := NIL
        END;
        
        IF (sym. id = S.else) THEN
          with. else := GetSym (with);
          with. elseStatm := StatementSeq (with)
        ELSE
          with. else := NIL;
          with. elseStatm := NIL
        END;
        with. end := CheckSym (with, S.end);
        RETURN with
        
      ELSIF (sym. id = S.exit) THEN
        NEW (exit);
        Init (exit);
        exit. exit := GetSym (exit);
        RETURN exit
        
      ELSIF (sym. id = S.return) THEN
        NEW (return);
        Init (return);
        return. return := GetSym (return);
        IF (sym. id < S.semicolon) THEN
          return. value := Expr (return)
        ELSE
          return. value := NIL
        END;
        RETURN return
        
      ELSE  (* empty statement *)
        NEW (statm);
        Init (statm);
        empty := TRUE;
        RETURN statm
      END
    END Statement;

  BEGIN
    first := Statement (up, empty);
    last := first;
    WHILE (sym. id = S.semicolon) DO
      last. semicolon := GetSym (last);
      statm := Statement (up, empty);
      statm. prev := last;
      last. next := statm;
      last := statm
    END;
    
    IF empty & (last. semicolon = NIL) THEN
      (* the last statement is completely empty; this confuses navigation
         through the tree using Next()/Prev(), so we better discard it *)
      IF (last. prev = NIL) THEN
        first := NIL
      ELSE
        last. prev. next := NIL;
        last. prev := NIL
      END
    END;
    
    RETURN first
  END StatementSeq;


PROCEDURE ^ FormalPars (up: AST.Node): AST.FormalPars;

PROCEDURE Type (up: AST.Node): AST.Type;
  VAR
    typeName: AST.TypeName;
    array: AST.Array;
    record: AST.Record;
    pointer: AST.Pointer;
    procType: AST.ProcType;
    fields, last: AST.Decl;
    
  PROCEDURE FieldList (up: AST.Record): AST.FieldList;
    VAR
      fieldList: AST.FieldList;
    BEGIN
      NEW (fieldList);
      fieldList. up := up;
      IF (sym. id = S.ident) THEN
        fieldList. name := IdentList (fieldList);
        fieldList. colon := CheckSym (fieldList, S.colon);
        fieldList. type := Type (fieldList);
      ELSE
        fieldList. name := NIL;
        fieldList. colon := NIL;
        fieldList. type := NIL
      END;
      fieldList. semicolon := NIL;
      fieldList. next := NIL;
      fieldList. prev := NIL;
      RETURN fieldList
    END FieldList;

  BEGIN
    IF (sym. id = S.ident) THEN
      NEW (typeName);
      typeName. up := up;
      typeName. struct := NIL;
      typeName. qualident := Qualident (typeName);
      RETURN typeName
      
    ELSIF (sym. id = S.array) THEN
      NEW (array);
      array. up := up;
      array. struct := NIL;
      array. array := GetSym (array);
      array. flags := Flags (array);
      IF (sym. id # S.of) THEN
        array. exprList := ExprList (array)
      ELSE
        array. exprList := NIL
      END;
      array. of := CheckSym (array, S.of);
      array. type := Type (array);
      RETURN array
      
    ELSIF (sym. id = S.record) THEN
      NEW (record);
      record. up := up;
      record. struct := NIL;
      record. record := GetSym (record);
      record. flags := Flags (record);
      IF (sym. id = S.lParen) THEN
        record. lParen := GetSym (record);
        record. base := Type (record);
        record. rParen := CheckSym (record, S.rParen)
      ELSE
        record. lParen := NIL;
        record. base := NIL;
        record. rParen := NIL
      END;
      
      record. fields := FieldList (record);
      last := record. fields;
      WHILE (sym. id = S.semicolon) DO
        last(AST.FieldList). semicolon := GetSym (last);
        fields := FieldList (record);
        fields. prev := last;
        last. next := fields;
        last := fields
      END;
      
      IF (last # NIL) & (last. name = NIL) & 
         (last(AST.FieldList). semicolon = NIL) THEN
        (* the last field list is completely empty; this confuses navigation
           through the tree using Next()/Prev(), so we better discard it *)
        IF (last. prev = NIL) THEN
          record. fields := NIL
        ELSE
          last. prev. next := NIL;
          last. prev := NIL
        END
      END;
      
      record. end := CheckSym (record, S.end);
      RETURN record
      
    ELSIF (sym. id = S.pointer) THEN
      NEW (pointer);
      pointer. up := up;
      pointer. struct := NIL;
      pointer. pointer := GetSym (pointer);
      pointer. flags := Flags (pointer);
      pointer. to := CheckSym (pointer, S.to);
      pointer. base := Type (pointer);
      RETURN pointer
      
    ELSIF (sym. id = S.procedure) THEN
      NEW (procType);
      procType. up := up;
      procType. struct := NIL;
      procType. procedure := GetSym (procType);
      procType. fpars := FormalPars (procType);
      RETURN procType
      
    ELSE
      SynErr (up); RETURN NIL
    END
  END Type;

PROCEDURE FormalPars (up: AST.Node): AST.FormalPars;
  VAR
    fpars: AST.FormalPars;
    last, fpSection: AST.FPSection;
    
  PROCEDURE FPSection (up: AST.Node): AST.FPSection;
    VAR
      fpSection: AST.FPSection;
    
    PROCEDURE GetDotsIdent (up: AST.FPSection): AST.IdentDef;
      VAR
        ident: AST.IdentDef;
      BEGIN
        NEW (ident);
        ident. up := up;
        ident. name := GetSym (ident);
        ident. mark := NIL;
        ident. flags := NIL;

        ident. comma := NIL;
        ident. next := NIL;
        ident. prev := NIL;
        ident. obj := NIL;
        ident. nextUse := NIL;
        ident. info := NIL;
        RETURN ident
      END GetDotsIdent;
    
    BEGIN
      NEW (fpSection);
      fpSection. up := up;
      fpSection. semicolon := NIL;
      fpSection. var := NIL;
      IF (sym. id = S.threeDots) THEN
        fpSection. name := GetDotsIdent (fpSection);
        fpSection. colon := NIL;
        fpSection. type := NIL
      ELSE
        IF (sym. id = S.var) THEN
          fpSection. var := GetSym (fpSection)
        END;
        fpSection. name := IdentList (fpSection);
        fpSection. colon := CheckSym(fpSection, S.colon);
        fpSection. type := Type (fpSection)
      END;
      fpSection.  next := NIL;
      fpSection.  prev := NIL;
      RETURN fpSection
    END FPSection;

  BEGIN
    NEW (fpars);
    fpars. Clear;                        (* set all fields to NIL *)
    fpars. up := up;
    fpars. flags := Flags (fpars);
    IF (sym. id = S.lParen) THEN
      fpars. lParen := CheckSym (fpars, S.lParen);
      IF (sym. id = S.ident) OR (sym. id = S.var) THEN

        fpars. fpSections := FPSection (fpars);
        last := fpars. fpSections;
        WHILE (sym. id = S.semicolon) DO
          last. semicolon := GetSym (last);
          fpSection := FPSection (fpars);
          fpSection. prev := last;
          last. next := fpSection;
          last := fpSection
        END
      END;
      fpars. rParen := CheckSym (fpars, S.rParen);
      IF (sym. id = S.colon) THEN
        fpars. colon := GetSym (fpars);
        fpars. resultType := Type (fpars)
      END
    END;
    RETURN fpars
  END FormalPars;

PROCEDURE ^ DeclSeq (VAR declSeq: AST.DeclSeq; up: AST.Body);

PROCEDURE Body (VAR body: AST.Body; up: AST.Node);
(* Body field has to be set in the enclosing procedure/module while still
   parsing it.  Otherwise the search procedures in module Decl will fail.
   Therefore the body isn't returned as a function result, but rather set 
   through a variable parameter.  *)
  BEGIN
    IF (sym. id = S.end) OR 
       (S. begin <= sym. id) & (sym. id <= S.procedure) THEN
      NEW (body);
      body. up := up;
      DeclSeq (body. declSeq, body);
  
      IF (sym. id = S.begin) THEN
        body. begin := GetSym (body);
        body. statmSeq := StatementSeq (body)
      ELSE
        body. begin := NIL;
        body. statmSeq := NIL
      END;
      body. end := CheckSym (body, S.end);
      body. name := Ident (body)
    ELSE
      SynErr (up); body := NIL
    END
  END Body;

PROCEDURE DeclSeq (VAR declSeq: AST.DeclSeq; up: AST.Body);
  VAR
    lastDecl: AST.Decl;
    
  PROCEDURE ProcDecl (up: AST.Node): AST.ProcDecl;
    VAR
      procDecl: AST.ProcDecl;
      hasBody: BOOLEAN;
    
    PROCEDURE Receiver (up: AST.ProcDecl): AST.FormalPars;
      VAR
        fpars: AST.FormalPars;
        fpsec: AST.FPSection;
      BEGIN
        NEW (fpars);
        fpars. Clear;
        fpars. up := up;
        fpars. flags := NIL;
        fpars. lParen := CheckSym (fpars, S.lParen);
        
        NEW (fpsec);
        fpsec. up := fpars;
        IF (sym. id = S.var) THEN
          fpsec. var := GetSym (fpsec)
        ELSE
          fpsec. var := NIL
        END;
        fpsec. name := IdentDef (fpsec, FALSE);
        fpsec. colon := CheckSym (fpsec, S.colon);
        IF ~(sym. id = S.ident) THEN
          SynErr (sym)
        ELSE
          fpsec. type := Type (fpsec)
        END;
        fpsec. semicolon := NIL;
        fpsec. prev := NIL;
        fpsec. next := NIL;
        
        fpars. fpSections := fpsec;
        fpars. rParen := CheckSym (fpars, S.rParen);
        fpars. colon := NIL;
        fpars. resultType := NIL;
        RETURN fpars
      END Receiver;
    
    BEGIN  (* pre: (sym. id = S.procedure) *)
      NEW (procDecl);
      procDecl. Clear;
      procDecl. up := up;
      procDecl. procedure := GetSym (procDecl);
      procDecl. body := NIL;
      hasBody := (sym. id # S.arrow);
      IF (sym. id = S.arrow)  THEN
        procDecl. arrow := GetSym (procDecl)
      ELSE
        procDecl. arrow := NIL
      END;
      IF (sym. id = S.lParen) THEN
        procDecl. receiver := Receiver (procDecl)
      ELSE
        procDecl. receiver := NIL
      END;
      procDecl. flags := Flags (procDecl);
      procDecl. name := IdentDef (procDecl, FALSE);
      procDecl. fpars := FormalPars (procDecl);
      procDecl. semicolon1 := CheckSym (procDecl, S.semicolon);
      
      hasBody := hasBody & 
                 (~interface OR FlagIsPresent (procDecl. flags, "HAS_BODY"));

      IF hasBody THEN
        Body (procDecl. body, procDecl);
        procDecl. semicolon2 := CheckSym (procDecl, S.semicolon)
      ELSE
        procDecl. body := NIL;
        procDecl. semicolon2 := NIL
      END;
      RETURN procDecl
    END ProcDecl;

  PROCEDURE VarDecl (up: AST.Body): AST. VarDecl;
    VAR
      varDecl: AST.VarDecl;
      ident, last: AST.IdentDef;
    BEGIN  (* pre: (sym. id = S.ident) *)
      NEW (varDecl);
      varDecl. Clear;
      varDecl. up := up;
      IF (sym. id = S.var) THEN
        varDecl. varKW := GetSym (varDecl)
      END;
      IF (sym. id = S.ident) THEN
        varDecl. name := IdentDef (varDecl, TRUE);
        last := varDecl. name;
        WHILE (sym. id = S.comma) DO
          last. comma := GetSym (last);
          ident := IdentDef (varDecl, TRUE);
          ident. prev := last;
          last. next := ident;
          last := ident
        END;
        varDecl. colon := CheckSym (varDecl, S.colon);
        varDecl. type := Type (varDecl);
        varDecl. semicolon := CheckSym (varDecl, S.semicolon)
      ELSE
        varDecl. name := NIL;
        varDecl. colon := NIL;
        varDecl. type := NIL;
        varDecl. semicolon := NIL
      END;
      RETURN varDecl
    END VarDecl;

  PROCEDURE TypeDecl (up: AST.Body): AST.TypeDecl;
    VAR
      typeDecl: AST.TypeDecl;
    BEGIN  (* pre: (sym=ident) *)
      NEW (typeDecl);
      typeDecl. Clear;
      typeDecl. up := up;
      IF (sym. id = S.type) THEN
        typeDecl. typeKW := GetSym (typeDecl)
      END;
      IF (sym. id = S.ident) THEN
        typeDecl. name := IdentDef (typeDecl, TRUE);
        typeDecl. equal := CheckSym (typeDecl, S.eql);
        typeDecl. type := Type (typeDecl);
        typeDecl. semicolon := CheckSym (typeDecl, S.semicolon)
      ELSE
        typeDecl. name := NIL;
        typeDecl. equal := NIL;
        typeDecl. type := NIL;
        typeDecl. semicolon := NIL
      END;
      RETURN typeDecl
    END TypeDecl;

  PROCEDURE ConstDecl (up: AST.Body): AST.ConstDecl;
    VAR
      constDecl: AST.ConstDecl;
    BEGIN  (* pre: (sym. id = S.ident) *)
      NEW (constDecl);
      constDecl. Clear;
      constDecl. up := up;
      IF (sym. id = S.const) THEN
        constDecl. constKW := GetSym (constDecl)
      END;
      IF (sym. id = S.ident) THEN
        constDecl. name := IdentDef (constDecl, TRUE);
        constDecl. equal := CheckSym (constDecl, S.eql);
        constDecl. value := Expr (constDecl);
        constDecl. semicolon := CheckSym (constDecl, S.semicolon)
      ELSE
        constDecl. name := NIL;
        constDecl. equal := NIL;
        constDecl. value := NIL;
        constDecl. semicolon := NIL
      END;
      RETURN constDecl
    END ConstDecl;

  PROCEDURE Append (decl: AST.Decl);
    BEGIN
      decl. next := NIL;
      decl. prev := lastDecl;
      IF (lastDecl = NIL) THEN
        declSeq := decl
      ELSE
        lastDecl. next := decl
      END;
      lastDecl := decl
    END Append;
  
  BEGIN
    declSeq := NIL; lastDecl := NIL;
    LOOP
      IF (sym. id = S.const) THEN
        WHILE (sym. id = S.ident) OR (sym. id = S.const) DO
          Append (ConstDecl (up))
        END
      ELSIF (sym. id = S.type) THEN
        WHILE (sym. id = S.ident) OR (sym. id = S.type) DO
          Append (TypeDecl (up))
        END
      ELSIF (sym. id = S.var) THEN
        WHILE (sym. id = S.ident) OR (sym. id = S.var) DO
          Append (VarDecl (up))
        END
      ELSE
        EXIT
      END
    END;
    WHILE (sym. id = S.procedure) DO
      Append (ProcDecl (up))
    END
  END DeclSeq;

PROCEDURE Module(): AST.Module;
  VAR
    module: AST.Module;
    importList: AST.ImportList;
    
  PROCEDURE ImportList (up: AST.Node): AST.Import;
    VAR
      import, list, last: AST.Import;
      found: BOOLEAN;
      i: INTEGER;
    BEGIN
      list := NIL;
      REPEAT
        NEW (import);
        import. up := up;
        import. comma := NIL;
        import. name := NIL;
        
        IF (list # NIL) THEN
          last. comma := CheckSym (last, S.comma)
        END;
        import. name := IdentDef (import, FALSE);
        IF (sym. id = S.becomes) THEN
          import. becomes := GetSym (import);
          import. module := Ident (import)
        ELSE
          import. becomes := NIL;
          import. module := import. name;
          NEW (import. name);
          import. name^ := import. module(AST.IdentDef)^;
          
          (* if the module name has multiple parts, use the last part for
             the name that is declared by the import statement *)
          Strings.FindPrev (S.moduleSeparator, import. name. name. str^,
                            MAX (INTEGER), found, i);
          IF found THEN
            NEW (import. name. name);
            import. name. name. Clear;
            S.StoreString (import. module. name. str^, import. name. name,
                           i+1, Strings.Length (import. module. name. str^))
          END
        END;
        
        import. next := NIL;
        IF (list = NIL) THEN
          import. prev := NIL;
          list := import
        ELSE
          import. prev := last;
          last. next := import
        END;
        last := import
      UNTIL (sym. id # S.comma);
      RETURN list
    END ImportList;

  BEGIN
    NEW (module);
    module. Clear;
    module. module := CheckSym (module, S.module);
    module. name := IdentDef (module, TRUE);
    interface := FlagIsPresent (module. name. flags, "INTERFACE") OR
                 FlagIsPresent (module. name. flags, "FOREIGN");
    module. semicolon1 := CheckSym (module, S.semicolon);
    module. body := NIL;
    IF (sym. id = S.import) THEN
      NEW (importList);
      importList. up := module;
      importList. import := GetSym (importList);
      importList. imports := NIL;
      importList. imports := ImportList (importList);
      importList. semicolon := CheckSym (importList, S.semicolon)
    ELSE
      importList := NIL
    END;
    module. importList := importList;
    IF (importList # NIL) THEN  (* store list in global variable *)
      import := importList. imports(AST.Import)
    ELSE
      import := NIL
    END;
    Body (module. body, module);
    module. period := CheckSym (module, S.period);
    module. next := NIL;
    module. prev := NIL;
    RETURN module
  END Module;


PROCEDURE ParseModule* (symbolList: S.StartSymbol): AST.Module;
  VAR
    module: AST.Module;
  BEGIN
    sym := symbolList. next;
    WHILE (sym # NIL) & (sym. id >= S.comment) DO
      sym := sym. next
    END;
    IF (sym = NIL) THEN
      SynErr (symbolList);
      RETURN NIL  (* never reached *)
    ELSE
      module := Module();
      module. startSymbol := symbolList;
      sym := NIL;
      RETURN module
    END
  END ParseModule;

BEGIN
  import := NIL;
  sym := NIL
END CNParser.
