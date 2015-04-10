(*	$Id: CNAST.Mod,v 1.5 1999/05/02 18:46:12 acken Exp $	*)
MODULE CNAST;
(*  Defintion of an abstract syntax tree based on the O2 syntax.
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
  S := CNScanner;


(* 

The records below define the nodes of an abstract syntax tree for an
Oberon-2 module.  Because the purpose of this tree is to serve as a
basis for text transformation, all syntactic sugar of the input module
is preserved, down to every single comma or semicolon.  Most of the
record types directly represent rules from the Oberon-2 EBNF syntax.
If in doubt over a record compare it against the syntax in the file
Oberon2-ps.Bnf.

The encoding of lists in the syntax varies.  In some places they are
replaced by recursion (like in Expr), in others by list contructions
(like in Designator or Case).  In the latter case the list terminator
(like "," for case labels) is an optional prefix part of a list
element.  Note that the internal representation of expressions differs
from the syntax.  There is no need for the internal representation to
encode the operator priorities like the EBNF syntax.

Record fields marked as `optional' represent optional branches of the
EBNF syntax.  They are NIL if the branch wasn't taken.

*)


TYPE
  Node* = S.Node;
  NodeDesc* = S.NodeDesc;
  Symbol* = S.Symbol;
  
TYPE  (* unparsed list of symbols, starting with "[" and ending with "]" *)
  FlagList* = POINTER TO FlagListDesc;
  FlagListDesc = RECORD
    (NodeDesc)
    first*, last*: S.Symbol;  (* first symbol is "[", last symbol "]" *)
  END;
  
TYPE  (* identifier or identifier followed by export mark *)
  Ident* = POINTER TO IdentDesc;
  IdentDesc = RECORD
    (NodeDesc)
    name*: S.Symbol;
    obj*: S.Info;                        (* filled in by module CNSymTab *)
    (* for an `IdentDef', this field refers to the defined object, for a simple
       `Ident' (i.e., a using occurence of an identifier) it refers to the
       referred declaration *)
    nextUse*: Ident;                     (* filled in by module CNSymTab *)
  END;

TYPE
  IdentDef* = POINTER TO IdentDefDesc;
  IdentDefDesc = RECORD
    (IdentDesc)
    mark*: S.Symbol;                     (* optional *)
    flags*: FlagList;                    (* opt; used in FPSection, VarDecl *)
    comma*: S.Symbol;                    (* optional; used for `IdentList' *)
    next*, prev*: IdentDef;              (* used to store `IdentList' *)
    info*: S.Info;                       (* used by some algorithms *)
  END;
  
TYPE  (* identifier list; never empty *)
  IdentDefList* = IdentDef;              (* uses `next', `prev' from `Ident' *)

TYPE  (* qualified or unqualified identifier *)
  Qualident* = POINTER TO QualidentDesc;
  QualidentDesc = RECORD
    (NodeDesc)
    module*: Ident;                      (* optional *)
    period*: S.Symbol;                   (* optional *)
    ident*: Ident;
  END;
  


(* Expressions
   ======================================================================== *)
   
TYPE
  Type* = POINTER TO TypeDesc;

TYPE  (* expression list; never empty *)
  Expr* = POINTER TO ExprDesc;
  ExprList* = Expr;

TYPE  (* designator and its list of selectors *)
  Selector* = POINTER TO SelectorDesc;  (* base type of designator selectors *)
  SelectorList* = Selector;
  SelectorDesc = RECORD
    (NodeDesc)
    next*, prev*: Selector;              (* used to store selector list *)
  END;
  Member* = POINTER TO MemberDesc;       (* field or type-bound procedure *)
  MemberDesc = RECORD
    (SelectorDesc)
    period*: S.Symbol;
    name*: Ident;
  END;
  Index* = POINTER TO IndexDesc;         (* array index (or index list) *)
  IndexDesc = RECORD
    (SelectorDesc)
    lBrak*: S.Symbol;
    exprList*: ExprList;
    rBrak*: S.Symbol;
  END;
  Deref* = POINTER TO DerefDesc;         (* pointer dereference *)
  DerefDesc = RECORD
    (SelectorDesc)
    arrow*: S.Symbol;
  END;
  TypeGuard* = POINTER TO TypeGuardDesc; (* type guard *)
  TypeGuardDesc = RECORD
    (SelectorDesc)
    lParen*: S.Symbol;
    type*: Type;
    rParen*: S.Symbol;
  END;
  Designator* = POINTER TO DesignatorDesc; (* designator *)
  DesignatorDesc = RECORD
    (NodeDesc)
    qualident*: Qualident;
    selectors*: SelectorList;            (* selector list; optional *)
  END;

TYPE  
  (* Expressions are mapped to two classes: `Operator' and `Factor'.  The first
     class is used for the syntactic rules Term, SimpleExpr, and Expr, and
     the second for the rule Factor.  Both classes share the base class
     `Expr'.  *)
  ExprDesc = RECORD
    (NodeDesc)
    comma*: S.Symbol;                    (* optional; used for `ExprList' *)
    next*, prev*: Expr;                  (* used to store `ExprList' *)
  END;

TYPE
  Operator* = POINTER TO OperatorDesc;
  OperatorDesc = RECORD
    (ExprDesc)
    (* there are two variants:
       dyadic operation : all three fields are filled
       monadic operation: `left' is NIL  *)
    left*: Expr;                         (* optional *)
    op*: S.Symbol;
    right*: Expr;
  END;

TYPE  (* factor and its variants; negation is encoded as part of `Expr' *)
  Factor* = POINTER TO FactorDesc;
  FactorDesc = RECORD
    (ExprDesc)
  END;
  FctCall* = POINTER TO FctCallDesc;
  FctCallDesc = RECORD
    (* this variant is also used for simple designators; in this case, all
       fields but `design' are NIL; as a side-effect, this allows to convert
       more easily an incorrectly detected type guard to a function call *)
    (FactorDesc)
    design*: Designator;
    lParen*: S.Symbol;                   (* optional *)
    arguments*: ExprList;                (* list of arguments; can be empty *)
    rParen*: S.Symbol;                   (* optional *)
  END;
  Literal* = POINTER TO LiteralDesc;
  LiteralDesc = RECORD
    (FactorDesc)
    literal*: S.Symbol;                  (* number, character, string, NIL *)
  END;
  FactorExpr* = POINTER TO FactorExprDesc;
  FactorExprDesc = RECORD
    (FactorDesc)
    lParen*: S.Symbol;
    expr*: Expr;
    rParen*: S.Symbol;
  END;
  
TYPE  (* set constructor *)
  SetElement* = POINTER TO SetElementDesc;
  SetElementDesc = RECORD
    (NodeDesc)
    lower*: Expr;
    upto*: S.Symbol;                     (* optional *)
    upper*: Expr;                        (* optional *)
    comma*: S.Symbol;                    (* optional *)
    next*, prev*: SetElement;            (* used to store element list *)
  END;
  Set* = POINTER TO SetDesc;
  SetDesc = RECORD
    (FactorDesc)
    qualident*: Qualident;               (* optional; for type qualified set *)
    lBrace*: S.Symbol;
    elements*: SetElement;               (* element list; possibly empty *)
    rBrace*: S.Symbol;
  END;


(* Statements
   ======================================================================== *)

TYPE  (* statement and its variants *)
  Statement* = POINTER TO StatementDesc;
  StatmSeq* = Statement;
  StatementDesc = RECORD
    (NodeDesc)
    semicolon*: S.Symbol;                (* optional *)
    (* Textually the semicolon is placed after its statement!  An instance of
       `Statement' represents the empty statement.  *)
    next*, prev*: Statement;             (* used to store statement seq *)
  END;
  
  Assignment* = POINTER TO AssignmentDesc; (* assignment *)
  AssignmentDesc = RECORD
    (StatementDesc)
    dest*: Designator;
    becomes*: S.Symbol;
    value*: Expr;
  END;
  
  ProcCall* = POINTER TO ProcCallDesc;   (* procedure call *)
  ProcCallDesc = RECORD
    (StatementDesc)
    proc*: Designator;
    lParen*: S.Symbol;                   (* optional *)
    arguments*: ExprList;                (* optional *)
    rParen*: S.Symbol;                   (* optional *)
  END;
  
  Elsif* = POINTER TO ElsifDesc;
  ElsifDesc = RECORD
    (NodeDesc)
    elsif*: S.Symbol;
    guard*: Expr;
    then*: S.Symbol;
    statmSeq*: StatmSeq;                 (* sequence of statements *)
    next*, prev*: Elsif;                 (* stores list of case branches *)
  END;
  If* = POINTER TO IfDesc;               (* IF statement *)
  IfDesc = RECORD
    (StatementDesc)
    if*: S.Symbol;
    guard*: Expr;
    then*: S.Symbol;
    statmSeq*: StatmSeq;                 (* sequence of statements *)
    elsifList*: Elsif;                   (* list of ELSIF parts; optional *)
    else*: S.Symbol;                     (* optional *)
    elseStatm*: StatmSeq;                (* optional ELSE statements *)
    end*: S.Symbol;
  END;
  
  CaseLabels* = POINTER TO CaseLabelsDesc;
  CaseLabelsList* = CaseLabels;
  CaseLabelsDesc = RECORD
    (NodeDesc)
    lower*: Expr;
    upto*: S.Symbol;                     (* optional *)
    upper*: Expr;                        (* optional *)
    comma*: S.Symbol;                    (* optional *)
    next*, prev*: CaseLabels;            (* stores list of case labels *)
  END;
  CaseBranch* = POINTER TO CaseBranchDesc;
  CaseBranchDesc = RECORD
    (NodeDesc)
    labels*: CaseLabels;                 (* list of case labels; optional *)
    colon*: S.Symbol;                    (* optional *)
    statmSeq*: StatmSeq;                 (* sequence of statements *)
    bar*: S.Symbol;                      (* optional *)
    next*, prev*: CaseBranch;            (* stores list of case branches *)
  END;
  Case* = POINTER TO CaseDesc;           (* CASE statement *)
  CaseDesc = RECORD
    (StatementDesc)
    case*: S.Symbol;
    selector*: Expr;
    of*: S.Symbol;
    branches*: CaseBranch;               (* list of branches; optional *)
    else*: S.Symbol;                     (* optional *)
    elseStatm*: StatmSeq;                (* optional ELSE statements *)
    end*: S.Symbol;
  END;
  
  While* = POINTER TO WhileDesc;         (* WHILE statement *)
  WhileDesc = RECORD
    (StatementDesc)
    while*: S.Symbol;
    guard*: Expr;
    do*: S.Symbol;
    statmSeq*: StatmSeq;                 (* list of  statements *)
    end*: S.Symbol;
  END;
  
  Repeat* = POINTER TO RepeatDesc;       (* REPEAT statement *)
  RepeatDesc = RECORD
    (StatementDesc)
    repeat*: S.Symbol;
    statmSeq*: StatmSeq;                 (* list of  statements *)
    until*: S.Symbol;
    guard*: Expr;
  END;
  
  For* = POINTER TO ForDesc;             (* FOR statement *)
  ForDesc = RECORD
    (StatementDesc)
    for*: S.Symbol;
    var*: Ident;
    becomes*: S.Symbol;
    lower*: Expr;
    to*: S.Symbol;
    upper*: Expr;
    by*: S.Symbol;                       (* optional *)
    step*: Expr;                         (* optional *)
    do*: S.Symbol;
    statmSeq*: StatmSeq;                 (* sequence of statements *)
    end*: S.Symbol;
  END;
  
  Loop* = POINTER TO LoopDesc;           (* LOOP statement *)
  LoopDesc = RECORD
    (StatementDesc)
    loop*: S.Symbol;
    statmSeq*: StatmSeq;                 (* sequence of statements *)
    end*: S.Symbol;
  END;
  
  WithBranch* = POINTER TO WithBranchDesc;
  WithBranchDesc = RECORD
    (NodeDesc)
    sep*: S.Symbol;                      (* "WITH" or "|" *)
    var*: Qualident;
    colon*: S.Symbol;
    type*: Type;
    do*: S.Symbol;
    statmSeq*: StatmSeq;                 (* sequence of statements *)
    next*, prev*: WithBranch;
  END;
  With* = POINTER TO WithDesc;           (* WITH statement *)
  WithDesc = RECORD
    (StatementDesc)
    branches*: WithBranch;               (* list of branches; never empty *)
    else*: S.Symbol;                     (* optional *)
    elseStatm*: StatmSeq;                (* optional ELSE statements *)
    end*: S.Symbol;
  END;
  
  Exit* = POINTER TO ExitDesc;           (* EXIT statement *)
  ExitDesc = RECORD
    (StatementDesc)
    exit*: S.Symbol;
  END;
  
  Return* = POINTER TO ReturnDesc;       (* RETURN statement *)
  ReturnDesc = RECORD
    (StatementDesc)
    return*: S.Symbol;
    value*: Expr;                        (* optional *)
  END;



(* Declarations
   ======================================================================== *)

TYPE  (* type constructors *)
  TypeDesc = RECORD
    (NodeDesc)
    struct*: S.Info;                     (* used by module CNSymTab *)
  END;

TYPE
  Decl* = POINTER TO DeclDesc;
  DeclSeq* = Decl;
  DeclDesc = RECORD
    (NodeDesc)
    next*, prev*: Decl;                  (* stores list of declarations *)
    name*: IdentDef;
    (* for variable, field, or parameter declaration the field `name'
       actually refers to a list, that is, to the first element of a
       IdentDefList  *)
  END;

TYPE
  TypeName* = POINTER TO TypeNameDesc;   (* type name *)
  TypeNameDesc = RECORD
    (TypeDesc)
    qualident*: Qualident;
  END;
  
  Array* = POINTER TO ArrayDesc;         (* array type *)
  ArrayDesc = RECORD
    (TypeDesc)
    array*: S.Symbol;
    flags*: FlagList;                    (* list of flags; optional *)
    exprList*: ExprList;                 (* list of lengths; optional *)
    of*: S.Symbol;
    type*: Type;
  END;
  
  FieldList* = POINTER TO FieldListDesc;
  FieldListDesc = RECORD
    (DeclDesc)
    colon*: S.Symbol;                    (* optional *)
    type*: Type;                         (* optional *)
    semicolon*: S.Symbol;                (* optional; used for list of flists*)
  END;
  Record* = POINTER TO RecordDesc;       (* record type *)
  RecordDesc = RECORD
    (TypeDesc)
    record*: S.Symbol;
    flags*: FlagList;                    (* list of flags; optional *)
    lParen*: S.Symbol;                   (* optional *)
    base*: Type;                         (* optional *)
    rParen*: S.Symbol;                   (* optional *)
    fields*: Decl;                       (* list of FieldList *)
    end*: S.Symbol;
  END;
  
  Pointer* = POINTER TO PointerDesc;     (* pointer type *)
  PointerDesc = RECORD
    (TypeDesc)
    pointer*: S.Symbol;
    flags*: FlagList;                    (* list of flags; optional *)
    to*: S.Symbol;
    base*: Type;
  END;
  
  FPSection* = POINTER TO FPSectionDesc;
  FPSectionDesc = RECORD
    (DeclDesc)
    var*: S.Symbol;                      (* optional *)
    colon*: S.Symbol;
    type*: Type;
    semicolon*: S.Symbol;                (* optional *)
    (* for the special parameter `...' used in C interfaces the field `name'
       refers to the dots symbol, while `var', `colon' and `type' are NIL  *)
  END;
  FormalPars* = POINTER TO FormalParsDesc;
  FormalParsDesc = RECORD
    (TypeDesc)
    flags*: FlagList;                    (* optional *)
    lParen*: S.Symbol;
    fpSections*: FPSection;              (* list of FPSection; optional *)
    rParen*: S.Symbol;
    colon*: S.Symbol;                    (* optional *)
    resultType*: Type;                   (* optional *)
    (* if the formal parameter list is not present, then all of the above
       fields are NIL, with the possible exception of field `flags' *)
  END;
  ProcType* = POINTER TO ProcTypeDesc;   (* procedure type *)
  ProcTypeDesc = RECORD
    (TypeDesc)
    procedure*: S.Symbol;
    fpars*: FormalPars;
  END;



(* Declarations
   ======================================================================== *)

(* types Decl, DeclDesc, and DeclSeq defined above *)

TYPE
  Scope* = POINTER TO ScopeDesc;         (* super class of module and proc *)
  ScopeDesc* = RECORD
    (DeclDesc)
  END;
  
TYPE
  Body* = POINTER TO BodyDesc;           (* module or procedure body *)
  BodyDesc = RECORD
    (NodeDesc)
    declSeq*: DeclSeq;                   (* list of declarations *)
    begin*: S.Symbol;                    (* optional *)
    statmSeq*: StatmSeq;                 (* sequence of statements; optional *)
    end*: S.Symbol;
    name*: Ident;
  END;

TYPE
  ProcDecl* = POINTER TO ProcDeclDesc;   (* procedure declaration *)
  ProcDeclDesc = RECORD
    (ScopeDesc)
    procedure*: S.Symbol;
    arrow*: S.Symbol;                    (* optional *)
    receiver*: FormalPars;               (* optional *)
    flags*: FlagList;                    (* optional *)
    fpars*: FormalPars;
    semicolon1*: S.Symbol;
    body*: Body;                         (* optional *)
    semicolon2*: S.Symbol;               (* optional *)
  END;
  
TYPE
  VarDecl* = POINTER TO VarDeclDesc;     (* variable declaration *)
  VarDeclDesc = RECORD
    (DeclDesc)
    varKW*: S.Symbol;                    (* optional *)
    colon*: S.Symbol;
    type*: Type;
    semicolon*: S.Symbol;
    (* note: it's also possible that all entries except for the keyword are
       NIL; that is, there is no need for a declaration to follow VAR *)
  END;
  
TYPE
  TypeDecl* = POINTER TO TypeDeclDesc;   (* type declaration *)
  TypeDeclDesc = RECORD
    (DeclDesc)
    typeKW*: S.Symbol;                   (* optional *)
    equal*: S.Symbol;
    type*: Type;
    semicolon*: S.Symbol;
    (* note: it's also possible that all entries except for the keyword are
       NIL; that is, there is no need for a declaration to follow TYPE *)
  END;
  
TYPE
  ConstDecl* = POINTER TO ConstDeclDesc; (* constant declaration *)
  ConstDeclDesc = RECORD
    (DeclDesc)
    constKW*: S.Symbol;                  (* optional *)
    equal*: S.Symbol;
    value*: Expr;
    semicolon*: S.Symbol;
    (* note: it's also possible that all entries except for the keyword are
       NIL; that is, there is no need for a declaration to follow CONST; the
       keyword can stand just for its own *)
  END;
  
TYPE
  Import* = POINTER TO ImportDesc;       (* import statement *)
  ImportDesc = RECORD
    (DeclDesc)                           (* base provides fields next, prev *)
    becomes*: S.Symbol;                  (* optional *)
    module*: Ident;                      (* _not_ optional *)
    comma*: S.Symbol;                    (* optional *)
  END;

TYPE
  ImportList* = POINTER TO ImportListDesc; (* import list *)
  ImportListDesc = RECORD
    (NodeDesc)
    import*: S.Symbol;
    imports*: Decl;
    semicolon*: S.Symbol;
  END;
  
TYPE
  Module* = POINTER TO ModuleDesc;
  ModuleDesc = RECORD
    (ScopeDesc)
    module*: S.Symbol;
    semicolon1*: S.Symbol;
    importList*: ImportList;             (* optional *)
    body*: Body;                         (* optional *)
    period*: S.Symbol;
    
    startSymbol*: S.StartSymbol;
  END;
  


PROCEDURE (n: FlagList) Clear*;
  BEGIN
    n. Clear^;
    n. first := NIL;
    n. last := NIL;
  END Clear;

PROCEDURE (n: Ident) Clear*;
  BEGIN
    n. Clear^;
    n. name := NIL;
    n. obj := NIL;
    n. nextUse := NIL;
  END Clear;

PROCEDURE (n: IdentDef) Clear*;
  BEGIN
    n. Clear^;
    n. mark := NIL;
    n. flags := NIL;
    n. comma := NIL;
    n. next := NIL;
    n. prev := NIL;
    n. info := NIL;
  END Clear;

PROCEDURE (n: Qualident) Clear*;
  BEGIN
    n. Clear^;
    n. module := NIL;
    n. period := NIL;
    n. ident := NIL;
  END Clear;

PROCEDURE (n: Selector) Clear*;
  BEGIN
    n. Clear^;
    n. next := NIL;
    n. prev := NIL;
  END Clear;

PROCEDURE (n: Member) Clear*;
  BEGIN
    n. Clear^;
    n. period := NIL;
    n. name := NIL;
  END Clear;

PROCEDURE (n: Index) Clear*;
  BEGIN
    n. Clear^;
    n. lBrak := NIL;
    n. exprList := NIL;
    n. rBrak := NIL;
  END Clear;

PROCEDURE (n: Deref) Clear*;
  BEGIN
    n. Clear^;
    n. arrow := NIL;
  END Clear;

PROCEDURE (n: TypeGuard) Clear*;
  BEGIN
    n. Clear^;
    n. lParen := NIL;
    n. type := NIL;
    n. rParen := NIL;
  END Clear;

PROCEDURE (n: Designator) Clear*;
  BEGIN
    n. Clear^;
    n. qualident := NIL;
    n. selectors := NIL;
  END Clear;

PROCEDURE (n: Expr) Clear*;
  BEGIN
    n. Clear^;
    n. comma := NIL;
    n. next := NIL;
    n. prev := NIL;
  END Clear;

PROCEDURE (n: Operator) Clear*;
  BEGIN
    n. Clear^;
    n. left := NIL;
    n. op := NIL;
    n. right := NIL;
  END Clear;

PROCEDURE (n: Factor) Clear*;
  BEGIN
    n. Clear^;
  END Clear;

PROCEDURE (n: FctCall) Clear*;
  BEGIN
    n. Clear^;
    n. design := NIL;
    n. lParen := NIL;
    n. arguments := NIL;
    n. rParen := NIL;
  END Clear;

PROCEDURE (n: Literal) Clear*;
  BEGIN
    n. Clear^;
    n. literal := NIL;
  END Clear;

PROCEDURE (n: FactorExpr) Clear*;
  BEGIN
    n. Clear^;
    n. lParen := NIL;
    n. expr := NIL;
    n. rParen := NIL;
  END Clear;

PROCEDURE (n: SetElement) Clear*;
  BEGIN
    n. Clear^;
    n. lower := NIL;
    n. upto := NIL;
    n. upper := NIL;
    n. comma := NIL;
    n. next := NIL;
    n. prev := NIL;
  END Clear;

PROCEDURE (n: Set) Clear*;
  BEGIN
    n. Clear^;
    n. qualident := NIL;
    n. lBrace := NIL;
    n. elements := NIL;
    n. rBrace := NIL;
  END Clear;

PROCEDURE (n: Statement) Clear*;
  BEGIN
    n. Clear^;
    n. semicolon := NIL;
    n. next := NIL;
    n. prev := NIL;
  END Clear;

PROCEDURE (n: Assignment) Clear*;
  BEGIN
    n. Clear^;
    n. dest := NIL;
    n. becomes := NIL;
    n. value := NIL;
  END Clear;

PROCEDURE (n: ProcCall) Clear*;
  BEGIN
    n. Clear^;
    n. proc := NIL;
    n. lParen := NIL;
    n. arguments := NIL;
    n. rParen := NIL;
  END Clear;

PROCEDURE (n: Elsif) Clear*;
  BEGIN
    n. Clear^;
    n. elsif := NIL;
    n. guard := NIL;
    n. then := NIL;
    n. statmSeq := NIL;
    n. next := NIL;
    n. prev := NIL;
  END Clear;

PROCEDURE (n: If) Clear*;
  BEGIN
    n. Clear^;
    n. if := NIL;
    n. guard := NIL;
    n. then := NIL;
    n. statmSeq := NIL;
    n. elsifList := NIL;
    n. else := NIL;
    n. elseStatm := NIL;
    n. end := NIL;
  END Clear;

PROCEDURE (n: CaseLabels) Clear*;
  BEGIN
    n. Clear^;
    n. lower := NIL;
    n. upto := NIL;
    n. upper := NIL;
    n. comma := NIL;
    n. next := NIL;
    n. prev := NIL;
  END Clear;

PROCEDURE (n: CaseBranch) Clear*;
  BEGIN
    n. Clear^;
    n. labels := NIL;
    n. colon := NIL;
    n. statmSeq := NIL;
    n. bar := NIL;
    n. next := NIL;
    n. prev := NIL;
  END Clear;

PROCEDURE (n: Case) Clear*;
  BEGIN
    n. Clear^;
    n. case := NIL;
    n. selector := NIL;
    n. of := NIL;
    n. branches := NIL;
    n. else := NIL;
    n. elseStatm := NIL;
    n. end := NIL;
  END Clear;

PROCEDURE (n: While) Clear*;
  BEGIN
    n. Clear^;
    n. while := NIL;
    n. guard := NIL;
    n. do := NIL;
    n. statmSeq := NIL;
    n. end := NIL;
  END Clear;

PROCEDURE (n: Repeat) Clear*;
  BEGIN
    n. Clear^;
    n. repeat := NIL;
    n. statmSeq := NIL;
    n. until := NIL;
    n. guard := NIL;
  END Clear;

PROCEDURE (n: For) Clear*;
  BEGIN
    n. Clear^;
    n. for := NIL;
    n. var := NIL;
    n. becomes := NIL;
    n. lower := NIL;
    n. to := NIL;
    n. upper := NIL;
    n. by := NIL;
    n. step := NIL;
    n. do := NIL;
    n. statmSeq := NIL;
    n. end := NIL;
  END Clear;

PROCEDURE (n: Loop) Clear*;
  BEGIN
    n. Clear^;
    n. loop := NIL;
    n. statmSeq := NIL;
    n. end := NIL;
  END Clear;

PROCEDURE (n: WithBranch) Clear*;
  BEGIN
    n. Clear^;
    n. sep := NIL;
    n. var := NIL;
    n. colon := NIL;
    n. type := NIL;
    n. do := NIL;
    n. statmSeq := NIL;
    n. next := NIL;
    n. prev := NIL;
  END Clear;

PROCEDURE (n: With) Clear*;
  BEGIN
    n. Clear^;
    n. branches := NIL;
    n. else := NIL;
    n. elseStatm := NIL;
    n. end := NIL;
  END Clear;

PROCEDURE (n: Exit) Clear*;
  BEGIN
    n. Clear^;
    n. exit := NIL;
  END Clear;

PROCEDURE (n: Return) Clear*;
  BEGIN
    n. Clear^;
    n. return := NIL;
    n. value := NIL;
  END Clear;

PROCEDURE (n: Type) Clear*;
  BEGIN
    n. Clear^;
    n. struct := NIL;
  END Clear;

PROCEDURE (n: Decl) Clear*;
  BEGIN
    n. Clear^;
    n. next := NIL;
    n. prev := NIL;
    n. name := NIL;
  END Clear;

PROCEDURE (n: TypeName) Clear*;
  BEGIN
    n. Clear^;
    n. qualident := NIL;
  END Clear;

PROCEDURE (n: Array) Clear*;
  BEGIN
    n. Clear^;
    n. array := NIL;
    n. flags := NIL;
    n. exprList := NIL;
    n. of := NIL;
    n. type := NIL;
  END Clear;

PROCEDURE (n: FieldList) Clear*;
  BEGIN
    n. Clear^;
    n. colon := NIL;
    n. type := NIL;
    n. semicolon := NIL;
    n. next := NIL;
    n. prev := NIL;
  END Clear;

PROCEDURE (n: Record) Clear*;
  BEGIN
    n. Clear^;
    n. record := NIL;
    n. flags := NIL;
    n. lParen := NIL;
    n. base := NIL;
    n. rParen := NIL;
    n. fields := NIL;
    n. end := NIL;
  END Clear;

PROCEDURE (n: Pointer) Clear*;
  BEGIN
    n. Clear^;
    n. pointer := NIL;
    n. flags := NIL;
    n. to := NIL;
    n. base := NIL;
  END Clear;

PROCEDURE (n: FPSection) Clear*;
  BEGIN
    n. Clear^;
    n. var := NIL;
    n. colon := NIL;
    n. type := NIL;
    n. semicolon := NIL;
  END Clear;

PROCEDURE (n: FormalPars) Clear*;
  BEGIN
    n. Clear^;
    n. flags := NIL;
    n. lParen := NIL;
    n. fpSections := NIL;
    n. rParen := NIL;
    n. colon := NIL;
    n. resultType := NIL;
  END Clear;

PROCEDURE (n: ProcType) Clear*;
  BEGIN
    n. Clear^;
    n. procedure := NIL;
    n. fpars := NIL;
  END Clear;

PROCEDURE (n: Scope) Clear*;
  BEGIN
    n. Clear^;
  END Clear;

PROCEDURE (n: Body) Clear*;
  BEGIN
    n. Clear^;
    n. declSeq := NIL;
    n. begin := NIL;
    n. statmSeq := NIL;
    n. end := NIL;
    n. name := NIL;
  END Clear;

PROCEDURE (n: ProcDecl) Clear*;
  BEGIN
    n. Clear^;
    n. procedure := NIL;
    n. arrow := NIL;
    n. receiver := NIL;
    n. flags := NIL;
    n. fpars := NIL;
    n. semicolon1 := NIL;
    n. body := NIL;
    n. semicolon2 := NIL;
  END Clear;

PROCEDURE (n: VarDecl) Clear*;
  BEGIN
    n. Clear^;
    n. varKW := NIL;
    n. colon := NIL;
    n. type := NIL;
    n. semicolon := NIL;
  END Clear;

PROCEDURE (n: TypeDecl) Clear*;
  BEGIN
    n. Clear^;
    n. typeKW := NIL;
    n. equal := NIL;
    n. type := NIL;
    n. semicolon := NIL;
  END Clear;

PROCEDURE (n: ConstDecl) Clear*;
  BEGIN
    n. Clear^;
    n. constKW := NIL;
    n. equal := NIL;
    n. value := NIL;
    n. semicolon := NIL;
  END Clear;
    
PROCEDURE (n: Import) Clear*;
  BEGIN
    n. Clear^;
    n. becomes := NIL;
    n. module := NIL;
    n. comma := NIL;
  END Clear;

PROCEDURE (n: ImportList) Clear*;
  BEGIN
    n. Clear^;
    n. import := NIL;
    n. imports := NIL;
    n. semicolon := NIL;
  END Clear;

PROCEDURE (n: Module) Clear*;
  BEGIN
    n. Clear^;
    n. module := NIL;
    n. semicolon1 := NIL;
    n. importList := NIL;
    n. body := NIL;
    n. period := NIL;
    n. startSymbol := NIL;
  END Clear;



PROCEDURE LastStatm (statmSeq: StatmSeq): Statement;
  BEGIN
    WHILE (statmSeq. next # NIL) DO
      statmSeq := statmSeq. next
    END;
    RETURN statmSeq
  END LastStatm;


PROCEDURE (n: FlagList) First*(): Node;
  BEGIN
    RETURN n. first
  END First;

PROCEDURE (n: FlagList) Last*(): Node;
  BEGIN
    RETURN n. last
  END Last;

PROCEDURE (n: Ident) First*(): Node;
  BEGIN
    RETURN n. name
  END First;

PROCEDURE (n: Ident) Last*(): Node;
  BEGIN
    RETURN n. name
  END Last;


PROCEDURE (n: IdentDef) First*(): Node;
  BEGIN
    RETURN n. name
  END First;

PROCEDURE (n: IdentDef) Last*(): Node;
  BEGIN
    IF (n. comma # NIL) THEN
      RETURN n. comma
    ELSIF (n. flags # NIL) THEN
      RETURN n. flags
    ELSIF (n. mark # NIL) THEN
      RETURN n. mark
    ELSE
      RETURN n. Last^()
    END
  END Last;


PROCEDURE (n: Qualident) First*(): Node;
  BEGIN
    IF (n. module # NIL) THEN
      RETURN n. module
    ELSE
      RETURN n. ident
    END
  END First;

PROCEDURE (n: Qualident) Last*(): Node;
  BEGIN
    RETURN n. ident
  END Last;


PROCEDURE (n: Selector) First*(): Node;
  BEGIN
    ASSERT (FALSE); RETURN NIL
  END First;

PROCEDURE (n: Selector) Last*(): Node;
  BEGIN
    ASSERT (FALSE); RETURN NIL
  END Last;


PROCEDURE (n: Member) First*(): Node;
  BEGIN
    RETURN n. period
  END First;

PROCEDURE (n: Member) Last*(): Node;
  BEGIN
    RETURN n. name
  END Last;


PROCEDURE (n: Index) First*(): Node;
  BEGIN
    RETURN n. lBrak
  END First;

PROCEDURE (n: Index) Last*(): Node;
  BEGIN
    RETURN n. rBrak
  END Last;


PROCEDURE (n: Deref) First*(): Node;
  BEGIN
    RETURN n. arrow
  END First;

PROCEDURE (n: Deref) Last*(): Node;
  BEGIN
    RETURN n. arrow
  END Last;


PROCEDURE (n: TypeGuard) First*(): Node;
  BEGIN
    RETURN n. lParen
  END First;

PROCEDURE (n: TypeGuard) Last*(): Node;
  BEGIN
    RETURN n. rParen
  END Last;


PROCEDURE (n: Designator) First*(): Node;
  BEGIN
    RETURN n. qualident
  END First;

PROCEDURE (n: Designator) Last*(): Node;
  VAR
    select: Selector;
  BEGIN
    select := n. selectors;
    IF (select = NIL) THEN
      RETURN n. qualident
    ELSE
      WHILE (select. next # NIL) DO
        select := select. next
      END;
      RETURN select
    END
  END Last;


PROCEDURE (n: Expr) First*(): Node;
  BEGIN
    ASSERT (FALSE); RETURN NIL
  END First;

PROCEDURE (n: Expr) Last*(): Node;
  BEGIN
    ASSERT (FALSE); RETURN NIL
  END Last;


PROCEDURE (n: Operator) First*(): Node;
  BEGIN
    IF (n. left = NIL) THEN
      RETURN n. op
    ELSE
      RETURN n. left
    END
  END First;

PROCEDURE (n: Operator) Last*(): Node;
  BEGIN
    IF (n. comma # NIL) THEN
      RETURN n. comma
    ELSE
      RETURN n. right
    END
  END Last;


PROCEDURE (n: Factor) First*(): Node;
  BEGIN
    ASSERT (FALSE); RETURN NIL
  END First;

PROCEDURE (n: Factor) Last*(): Node;
  BEGIN
    ASSERT (FALSE); RETURN NIL
  END Last;


PROCEDURE (n: FctCall) First*(): Node;
  BEGIN
    RETURN n. design
  END First;

PROCEDURE (n: FctCall) Last*(): Node;
  BEGIN
    IF (n. comma # NIL) THEN
      RETURN n. comma
    ELSIF (n. rParen # NIL) THEN
      RETURN n. rParen
    ELSE
      RETURN n. design
    END
  END Last;


PROCEDURE (n: Literal) First*(): Node;
  BEGIN
    RETURN n. literal
  END First;

PROCEDURE (n: Literal) Last*(): Node;
  BEGIN
    IF (n. comma # NIL) THEN
      RETURN n. comma
    ELSE
      RETURN n. literal
    END
  END Last;


PROCEDURE (n: FactorExpr) First*(): Node;
  BEGIN
    RETURN n. lParen
  END First;

PROCEDURE (n: FactorExpr) Last*(): Node;
  BEGIN
    IF (n. comma # NIL) THEN
      RETURN n. comma
    ELSE
      RETURN n. rParen
    END
  END Last;


PROCEDURE (n: SetElement) First*(): Node;
  BEGIN
    RETURN n. lower
  END First;

PROCEDURE (n: SetElement) Last*(): Node;
  BEGIN
    IF (n. comma # NIL) THEN
      RETURN n. comma
    ELSIF (n. upper # NIL) THEN
      RETURN n. upper
    ELSE
      RETURN n. lower
    END
  END Last;


PROCEDURE (n: Set) First*(): Node;
  BEGIN
    IF (n. qualident # NIL) THEN
      RETURN n. qualident. First()
    ELSE
      RETURN n. lBrace
    END
  END First;

PROCEDURE (n: Set) Last*(): Node;
  BEGIN
    IF (n. comma # NIL) THEN
      RETURN n. comma
    ELSE
      RETURN n. rBrace
    END
  END Last;


PROCEDURE (n: Statement) First*(): Node;
  BEGIN  (* empty statement *)
    RETURN n. semicolon
  END First;

PROCEDURE (n: Statement) Last*(): Node;
  BEGIN  (* empty statement *)
    RETURN n. semicolon
  END Last;


PROCEDURE (n: Assignment) First*(): Node;
  BEGIN
    RETURN n. dest
  END First;

PROCEDURE (n: Assignment) Last*(): Node;
  BEGIN
    IF (n. semicolon # NIL) THEN
      RETURN n. semicolon
    ELSE
      RETURN n. value
    END
  END Last;

PROCEDURE (n: ProcCall) First*(): Node;
  BEGIN
    RETURN n. proc
  END First;

PROCEDURE (n: ProcCall) Last*(): Node;
  BEGIN
    IF (n. semicolon # NIL) THEN
      RETURN n. semicolon
    ELSIF (n. rParen # NIL) THEN
      RETURN n. rParen
    ELSE
      RETURN n. proc
    END
  END Last;


PROCEDURE (n: Elsif) First*(): Node;
  BEGIN
    RETURN n. elsif
  END First;

PROCEDURE (n: Elsif) Last*(): Node;
  BEGIN
    IF (n. statmSeq # NIL) THEN
      RETURN LastStatm (n. statmSeq)
    ELSE
      RETURN n. then
    END
  END Last;


PROCEDURE (n: If) First*(): Node;
  BEGIN
    RETURN n. if
  END First;

PROCEDURE (n: If) Last*(): Node;
  BEGIN
    IF (n. semicolon # NIL) THEN
      RETURN n. semicolon
    ELSE
      RETURN n. end
    END
  END Last;


PROCEDURE (n: CaseLabels) First*(): Node;
  BEGIN
    RETURN n. lower
  END First;

PROCEDURE (n: CaseLabels) Last*(): Node;
  BEGIN
    IF (n. comma # NIL) THEN
      RETURN n. comma
    ELSIF (n. upper # NIL) THEN
      RETURN n. upper
    ELSE
      RETURN n. lower
    END
  END Last;


PROCEDURE (n: CaseBranch) First*(): Node;
  BEGIN
    IF (n. labels # NIL) THEN
      RETURN n. labels
    ELSIF (n. statmSeq # NIL) THEN
      RETURN n. statmSeq
    ELSE
      ASSERT (n. bar # NIL);
      RETURN n. bar
    END
  END First;

PROCEDURE (n: CaseBranch) Last*(): Node;
  BEGIN
    IF (n. bar # NIL) THEN
      RETURN n. bar
    ELSIF (n. statmSeq # NIL) THEN
      RETURN LastStatm (n. statmSeq)
    ELSE
      ASSERT (n. colon # NIL);
      RETURN n. colon
    END
  END Last;


PROCEDURE (n: Case) First*(): Node;
  BEGIN
    RETURN n. case
  END First;

PROCEDURE (n: Case) Last*(): Node;
  BEGIN
    IF (n. semicolon # NIL) THEN
      RETURN n. semicolon
    ELSE
      RETURN n. end
    END
  END Last;


PROCEDURE (n: While) First*(): Node;
  BEGIN
    RETURN n. while
  END First;

PROCEDURE (n: While) Last*(): Node;
  BEGIN
    IF (n. semicolon # NIL) THEN
      RETURN n. semicolon
    ELSE
      RETURN n. end
    END
  END Last;


PROCEDURE (n: Repeat) First*(): Node;
  BEGIN
    RETURN n. repeat
  END First;

PROCEDURE (n: Repeat) Last*(): Node;
  BEGIN
    IF (n. semicolon # NIL) THEN
      RETURN n. semicolon
    ELSE
      RETURN n. guard
    END
  END Last;


PROCEDURE (n: For) First*(): Node;
  BEGIN
    RETURN n. for
  END First;

PROCEDURE (n: For) Last*(): Node;
  BEGIN
    IF (n. semicolon # NIL) THEN
      RETURN n. semicolon
    ELSE
      RETURN n. end
    END
  END Last;


PROCEDURE (n: Loop) First*(): Node;
  BEGIN
    RETURN n. loop
  END First;

PROCEDURE (n: Loop) Last*(): Node;
  BEGIN
    IF (n. semicolon # NIL) THEN
      RETURN n. semicolon
    ELSE
      RETURN n. end
    END
  END Last;


PROCEDURE (n: WithBranch) First*(): Node;
  BEGIN
    RETURN n. sep
  END First;

PROCEDURE (n: WithBranch) Last*(): Node;
  BEGIN
    IF (n. statmSeq # NIL) THEN
      RETURN LastStatm (n. statmSeq)
    ELSE
      RETURN n. do
    END
  END Last;


PROCEDURE (n: With) First*(): Node;
  BEGIN
    RETURN n. branches
  END First;

PROCEDURE (n: With) Last*(): Node;
  BEGIN
    IF (n. semicolon # NIL) THEN
      RETURN n. semicolon
    ELSE
      RETURN n. end
    END
  END Last;


PROCEDURE (n: Exit) First*(): Node;
  BEGIN
    RETURN n. exit
  END First;

PROCEDURE (n: Exit) Last*(): Node;
  BEGIN
    IF (n. semicolon # NIL) THEN
      RETURN n. semicolon
    ELSE
      RETURN n. exit
    END
  END Last;


PROCEDURE (n: Return) First*(): Node;
  BEGIN
    RETURN n. return
  END First;

PROCEDURE (n: Return) Last*(): Node;
  BEGIN
    IF (n. semicolon # NIL) THEN
      RETURN n. semicolon
    ELSIF (n. value # NIL) THEN
      RETURN n. value
    ELSE
      RETURN n. return
    END
  END Last;


PROCEDURE (n: Type) First*(): Node;
  BEGIN
    ASSERT (FALSE); RETURN NIL
  END First;

PROCEDURE (n: Type) Last*(): Node;
  BEGIN
    ASSERT (FALSE); RETURN NIL
  END Last;


PROCEDURE (n: Decl) First*(): Node;
  BEGIN
    ASSERT (FALSE); RETURN NIL
  END First;

PROCEDURE (n: Decl) Last*(): Node;
  BEGIN
    ASSERT (FALSE); RETURN NIL
  END Last;


PROCEDURE (n: TypeName) First*(): Node;
  BEGIN
    RETURN n. qualident
  END First;

PROCEDURE (n: TypeName) Last*(): Node;
  BEGIN
    RETURN n. qualident
  END Last;


PROCEDURE (n: Array) First*(): Node;
  BEGIN
    RETURN n. array
  END First;

PROCEDURE (n: Array) Last*(): Node;
  BEGIN
    RETURN n. type
  END Last;


PROCEDURE (n: FieldList) First*(): Node;
  BEGIN
    IF (n. name # NIL) THEN
      RETURN n. name
    ELSE
      RETURN n. semicolon
    END
  END First;

PROCEDURE (n: FieldList) Last*(): Node;
  BEGIN
    IF (n. semicolon # NIL) THEN
      RETURN n. semicolon
    ELSE
      ASSERT (n. type # NIL);
      RETURN n. type
    END
  END Last;


PROCEDURE (n: Record) First*(): Node;
  BEGIN
    RETURN n. record
  END First;

PROCEDURE (n: Record) Last*(): Node;
  BEGIN
    RETURN n. end
  END Last;


PROCEDURE (n: Pointer) First*(): Node;
  BEGIN
    RETURN n. pointer
  END First;

PROCEDURE (n: Pointer) Last*(): Node;
  BEGIN
    RETURN n. base
  END Last;


PROCEDURE (n: FPSection) First*(): Node;
  BEGIN
    IF (n. var # NIL) THEN
      RETURN n. var
    ELSE
      RETURN n. name
    END
  END First;

PROCEDURE (n: FPSection) Last*(): Node;
  BEGIN
    IF (n. semicolon # NIL) THEN
      RETURN n. semicolon
    ELSIF (n. type # NIL) THEN
      RETURN n. type
    ELSE
      RETURN n. name  (* special parameter `...' *)
    END
  END Last;


PROCEDURE (n: FormalPars) First*(): Node;
  BEGIN
    IF (n. flags # NIL) THEN
      RETURN n. flags
    ELSE
      RETURN n. lParen
    END
  END First;

PROCEDURE (n: FormalPars) Last*(): Node;
  BEGIN
    IF (n. resultType # NIL) THEN
      RETURN n. resultType
    ELSE
      RETURN n. rParen
    END
  END Last;


PROCEDURE (n: ProcType) First*(): Node;
  BEGIN
    RETURN n. procedure
  END First;

PROCEDURE (n: ProcType) Last*(): Node;
  BEGIN
    IF (n. fpars. lParen # NIL) OR (n. fpars. flags # NIL) THEN
      RETURN n. fpars
    ELSE
      RETURN n. procedure
    END
  END Last;


PROCEDURE (n: Scope) First*(): Node;
  BEGIN
    ASSERT (FALSE); RETURN NIL
  END First;

PROCEDURE (n: Scope) Last*(): Node;
  BEGIN
    ASSERT (FALSE); RETURN NIL
  END Last;


PROCEDURE (n: Body) First*(): Node;
  BEGIN
    IF (n. declSeq # NIL) THEN
      RETURN n. declSeq
    ELSIF (n. begin # NIL) THEN
      RETURN n. begin
    ELSE
      RETURN n. end
    END
  END First;

PROCEDURE (n: Body) Last*(): Node;
  BEGIN
    RETURN n. name
  END Last;


PROCEDURE (n: ProcDecl) First*(): Node;
  BEGIN
    RETURN n. procedure
  END First;

PROCEDURE (n: ProcDecl) Last*(): Node;
  BEGIN
    IF (n. semicolon2 # NIL) THEN
      RETURN n. semicolon2
    ELSE
      RETURN n. semicolon1
    END
  END Last;


PROCEDURE (n: VarDecl) First*(): Node;
  BEGIN
    IF (n. varKW # NIL) THEN
      RETURN n. varKW
    ELSE
      RETURN n. name
    END
  END First;

PROCEDURE (n: VarDecl) Last*(): Node;
  BEGIN
    IF (n. semicolon # NIL) THEN
      RETURN n. semicolon
    ELSE
      RETURN n. varKW
    END
  END Last;


PROCEDURE (n: TypeDecl) First*(): Node;
  BEGIN
    IF (n. typeKW # NIL) THEN
      RETURN n. typeKW
    ELSE
      RETURN n. name
    END
  END First;

PROCEDURE (n: TypeDecl) Last*(): Node;
  BEGIN
    IF (n. semicolon # NIL) THEN
      RETURN n. semicolon
    ELSE
      RETURN n. typeKW
    END
  END Last;


PROCEDURE (n: ConstDecl) First*(): Node;
  BEGIN
    IF (n. constKW # NIL) THEN
      RETURN n. constKW
    ELSE
      RETURN n. name
    END
  END First;
    
PROCEDURE (n: ConstDecl) Last*(): Node;
  BEGIN
    IF (n. semicolon # NIL) THEN
      RETURN n. semicolon
    ELSE
      RETURN n. constKW
    END
  END Last;


PROCEDURE (n: Import) First*(): Node;
  BEGIN
    IF (n. becomes # NIL) THEN
      RETURN n. name
    ELSE
      RETURN n. module
    END
  END First;

PROCEDURE (n: Import) Last*(): Node;
  BEGIN
    IF (n. comma # NIL) THEN
      RETURN n. comma
    ELSE
      RETURN n. module
    END
  END Last;


PROCEDURE (n: ImportList) First*(): Node;
  BEGIN
    RETURN n. import
  END First;

PROCEDURE (n: ImportList) Last*(): Node;
  BEGIN
    RETURN n. semicolon
  END Last;


PROCEDURE (n: Module) First*(): Node;
  BEGIN
    RETURN n. module
  END First;

PROCEDURE (n: Module) Last*(): Node;
  BEGIN
    RETURN n. period
  END Last;



PROCEDURE (s: Selector) FirstSym* (): Symbol;
  BEGIN
    WITH s: Member DO
      RETURN s. period
    | s: Index DO
      RETURN s. lBrak
    | s: Deref DO
      RETURN s. arrow
    | s: TypeGuard DO
      RETURN s. lParen
    END
  END FirstSym;


PROCEDURE RemoveAST* (VAR ast: Module);
(* Remove AST data structure.  Note that all symbols are discarded as well.  *)
  VAR
    s, next: Symbol;
    node, up: Node;
  BEGIN
    s := ast. startSymbol;
    WHILE (s # NIL) DO
      node := s. up;
      WHILE (node # NIL) DO
        up := node. up;
        node. Clear;
        node := up
      END;
      next := s. next;
      s. Clear;
      s := next
    END;
    ast := NIL
  END RemoveAST;


PROCEDURE TestFirstLast* (ast: Module);
(* This procedure checks if the `First', `Last', `Next' and `Prev' methods
   work as they should for the given syntax tree.  It is quite useful when
   looking for invalid structures in the tree, although it does not catch
   all possible errors.  *)
  VAR
    lastSym: Symbol;
    
  PROCEDURE TraverseForward (node: Node);
    VAR
      n: Node;
    BEGIN
      WITH node: Symbol DO
        ASSERT (node. PrevSym() = lastSym);
        lastSym := node
      ELSE
        n := node. First();
        WHILE (n # NIL) DO
(*IF n. up # node THEN
Log.Type ("node", node);
Log.Type ("n", n);
Log.Ptr ("n", n);
Log.Type ("n.up", n.up);
END;*)
          ASSERT (n. up = node);
          TraverseForward (n);
          n := node. Next (n)
        END
      END
    END TraverseForward;
  
  PROCEDURE TraverseBackward (node: Node);
    VAR
      n: Node;
    BEGIN
      WITH node: Symbol DO
        ASSERT (node. NextSym() = lastSym);
        lastSym := node
      ELSE
        n := node. Last();
        WHILE (n # NIL) DO
          ASSERT (n. up = node);
          TraverseBackward (n);
          n := node. Prev (n)
        END
      END
    END TraverseBackward;
  
  BEGIN
    ASSERT (ast. First() = ast. module);
    lastSym := NIL;
    TraverseForward (ast);
    ASSERT (lastSym = ast. period);
    
    ASSERT (ast. Last() = ast. period);
    lastSym := NIL;
    TraverseBackward (ast);
    ASSERT (lastSym = ast. module)
  END TestFirstLast;

END CNAST.
