(* 	$Id: CNScanner.Mod,v 1.13 1999/11/14 18:17:08 ooc-devel Exp $	 *)
MODULE CNScanner;
(*  Lexical scanner for Oberon-2 source code.
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
  Out, Channel, Files, Strings, Ascii, CharClass, IntStr,
  Param := Parameter, ParamPaths, ParamOptions, ParamPragmas, VC := RCS, 
  Output := CNOutput;



(*

File positions are stored as (line, column) tuples.  Line 1, column 1
refers to the first position of the file.  The position of the end of
a symbol refers to the character just to the right of the character in
question.

Example: A symbol `MODULE' in the first line of a file would have a
starting position of (1,1), and an ending position of (7,1).

Note that for most purposes absolute text coordinates are of little
use.  Therefore this module exports a procedure `Abs2Rel' to convert
them into coordinates relative to the end of the preceding symbol.

Symbols can only be part of a single line, with the exception of the
special symbols representing comments or pragmas.  That is, for normal
symbols the line number of both starting and ending position is equal.
In this case the length of the symbol is equal to the difference of
the column numbers of the ending and starting positions.

Comments and pragmas are white space when translating a module.  For
purposes of text rewriting they can't be ignored.  Therefore the
scanner includes them as separate entities in the symbol stream.  They
are stored as text blocks which include the starting and ending
delimiter of the contruct.  A comment starts with `(*' and ends with
the matching `*)', including any nested comments or pragmas within.
The same holds for pragmas.  Additionally program text that is
disabled due to conditional compilation is included in the enclosing
pragma's text block.

*)

TYPE
  String* = Param.String;
  Filename* = Param.Filename;
  
CONST  (* symbolic values for `Symbol.id': *)
  (* token identifications *)
  times*=1; slash*=2; div*=3; mod*=4;
  and*=5; plus*=6; minus*=7; or*=8; eql*=9;
  neq*=10; lss*=11; leq*=12; gtr*=13; geq*=14;
  in*=15; is*=16; arrow*=17; period*=18; comma*=19;
  colon*=20; upto*=21; rParen*=22; rBrak*=23; rBrace*=24;
  of*=25; then*=26; do*=27; to*=28; by*=29; lParen*=30;
  lBrak*=31; lBrace*=32; not*=33; becomes*=34; number*=35;
  nil*=36; string*=37; ident*=38; semicolon*=39;
  bar*=40; end*=41; else*=42; elsif*=43; until*=44;
  if*=45; case*=46; while*=47; repeat*=48; loop*=49;
  for*=50; with*=51; exit*=52; return*=53;
  array*=54; record*=55; pointer*=56; begin*=57; const*=58;
  type*=59; var*=60; procedure*=61;
  import*=62; module*=63; endOfFile*=64;
  (* nonstandard symbols & symbols normally mapped to whitespace; the predicate
     to test for whitespace is  symId>=comment  *)
  threeDots*=65; comment*=66; pragma*=67; 
  (* symbols `<*' and `*>', internal use only *)
  pragmaStart=69; pragmaEnd=70;

TYPE  (* common base type of abstract syntax tree and symbol table *)
  Info* = POINTER TO InfoDesc;
  InfoDesc* = RECORD
  END;
  
TYPE  (* base class for types defined in module AST *)
  Node* = POINTER TO NodeDesc;
  NodeDesc* = RECORD
    (InfoDesc)
    up*: Node;                           (* next higher node *)
  END;

TYPE
  Symbol* = POINTER TO SymbolDesc;
  SymbolDesc = RECORD
    (NodeDesc)
    next-, prev-: Symbol;    (* pointers for list created by this module *)
    line-, column-: LONGINT; (* symbol position; line and column >= 1; first
                                read as absolute values, but most algorithms
                                convert this to relative coordinates *)
    pos-: LONGINT;           (*  dito, counted in characters starting with 0;
                                 unlike (line,column) this field will not 
                                 change once the symbol is created *)
    id-: SHORTINT;           (* what kind of symbol? *)
    str-: String;            (* string representation of symbol *)
    (* length of symbol: initially LEN(str^)-1 *)
  END;
  LinePos* = POINTER TO ARRAY OF LONGINT;
  StartSymbol* = POINTER TO StartSymbolDesc;
  StartSymbolDesc = RECORD
    (SymbolDesc)
    file-: String;           (* name of source file *)
    lines: LONGINT;          (* number of lines in original source file *)
    linePos: LinePos;        (* list with starting position of every line *)
  END;
  TextSymbol* = POINTER TO TextSymbolDesc;
  TextSymbolDesc = RECORD
    (SymbolDesc)
    endLine-, endColumn-: LONGINT;  (* position just after end of symbol *)
    info*: Info;
  END;
  NumberSymbol* = POINTER TO NumberSymbolDesc;
  NumberSymbolDesc = RECORD
    (SymbolDesc)
    numType: SHORTINT;       (* numInt, numReal or numLReal *)
    intVal: LONGINT;         (* value of integer constant *)
  END;
  

CONST
  undefStr* = "???";
  undefPos* = -1;
  
VAR
  undefSym*: Symbol;

VAR
  moduleIdent: BOOLEAN;
  (* if TRUE, then identifiers can contain the character `moduleSeparator';
     if \w designates a character, and ":" is the separator, a module 
     identifier must satisfy the regular expression "\w+(:\w+)*" *)

CONST
  moduleSeparator* = ":";
  (* with `moduleIdent=TRUE', identifiers can contain this character; this
     means that an identifier can look like "foo:bar:M"; illegal variants
     (like ":foo", "foo:", or "foo::bar") are detected by the scanner and
     marked as faulty *)
     
VAR
  (* this is the pragma state that holds before parsing of a module starts; it
     has to be stored after all options have been parsed, but before the first
     symbol is read from a source file *)
  pragmas*: ParamPragmas.PragmaState;


CONST
  numInt=1; numReal=2; numLReal=3;  
  (* values for `Symbol.numType', set by `GetSym' *)

VAR
  sym: Symbol;                          (* current token, set by `GetSym' *)
  sourceFile: String;                   (* name of current input file *)
  startSymbol: StartSymbol;             (* first element of symbol list *)

CONST
  eof = 00X;                             
  (* end of file marker, always appended to the buffer by `Init' *)
  sizeKWTable = 128;                     
  (* size of keyword hash table *)
  sizeBlock = 2*1024;
  (* number of bytes read per chunk if `incrementalRead' is TRUE *)
  
  initLinePos = 252;  (* size of first `LinePos' array *)
  incrLinePos = 256;  (* increment if buffer overflows *)
  
VAR
  kwStr: ARRAY sizeKWTable, 2 OF String; 
  (* hash table for keywords, used bz `Ident' *)
  kwSym: ARRAY sizeKWTable, 2 OF SHORTINT; 
  (* token for associated keywords (values for `sym') *)

  incrementalRead: BOOLEAN;
  (* read files in chunks of `sizeBlock' bytes (used for make to scan sources
     without having to read all of the file) *)
  buf: String;
  (* buffer area, used to hold the whole file *)
  pos: LONGINT;                          
  (* current scanning position in `buf' *)
  currLine: LONGINT;
  (* current line number of `pos', starting at 1 *)
  currLinePos: LONGINT;
  (* position of the first character of the current line *)
  currLineTab: LONGINT;
  (* difference between column and character position due to tab chars *)
  fileLen: LONGINT;
  (* length of input file in bytes *)
  currLen: LONGINT;
  (* number of bytes that have been read from the file; until the end of the 
     file is reached, the relation `currLen-pos >= sizeBlock DIV 2' holds with
     every call of `GetSym' *)
  inFile: Files.File;
  inReader: Channel.Reader;
  (* file and rider on input file *)

TYPE 
  ConditionStack = POINTER TO ConditionStackDesc;
  ConditionStackDesc = RECORD
    prev: ConditionStack;
    (* link to preceding item in stack, top of stack is in `condStack' *)
    ifPos: LONGINT;
    (* position of initial `IF' keyword *)
    skippedCond: BOOLEAN;
    (* TRUE iff whole condition is part of skipped text *)
    foundTrue: BOOLEAN;
    (* TRUE iff a preceding IF or ELSIF guard evaluated to TRUE *)
    elsePresent: BOOLEAN;
    (* set when an ELSE part has been parsed *)
  END;

CONST  (* values for `scanStatus' *)
  normal = 0;                            (* scanning Oberon-2 code *)
  inPragma = 1;                          (* scanning between <* *> *)
  skippingText = 2;                      (* skipping Oberon-2 code *)
  
VAR
  condStack: ConditionStack;
  (* stack of conditional statements *)
  scanStatus: SHORTINT;
  (* scanning status (see values above) *)
  

CONST
  sizeStringTable = sizeKWTable;
TYPE
  StringArray = POINTER TO ARRAY OF String;
VAR
  stringTable: ARRAY sizeStringTable OF StringArray;


CONST
  tabWidth* = 8;



PROCEDURE (n: Symbol) NextSym* (): Symbol;
(* Returns the next non-whitespace symbol following `n', or NIL if no such
   symbol exists.  *)
  BEGIN
    sym := n;
    REPEAT
      sym := sym. next
    UNTIL (sym = NIL) OR
          (sym. id # comment) & (sym. id # pragma);
    RETURN sym
  END NextSym;

PROCEDURE (n: Symbol) PrevSym* (): Symbol;
(* Analogous to `NextSym'.  *)
  BEGIN
    sym := n;
    REPEAT
      sym := sym. prev
    UNTIL (sym = NIL) OR
          (sym. id # comment) & (sym. id # pragma);
    IF (sym IS StartSymbol) THEN
      RETURN NIL
    ELSE
      RETURN sym
    END
  END PrevSym;


PROCEDURE (n: Node) Clear*;
  BEGIN
    n. up := NIL
  END Clear;

PROCEDURE (n: Node) First*(): Node;
(* Returns the first part of the node `n' with regard to the syntax.  The
   result is only NIL if `n' is an instance of `Symbol'.  *)
  BEGIN
    ASSERT (FALSE); RETURN NIL
  END First;

PROCEDURE (n: Node) Last*(): Node;
(* Analogous to `First'.  *)
  BEGIN
    ASSERT (FALSE); RETURN NIL
  END Last;

PROCEDURE (n: Node) FirstSym* (): Symbol;
(* Returns first symbol of node `n'.  *)
  BEGIN
    WHILE ~(n IS Symbol) DO
      n := n. First()
    END;
    RETURN n(Symbol)
  END FirstSym;

PROCEDURE (n: Node) LastSym* (): Symbol;
(* Analogous to `FirstSym'.  *)
  BEGIN
    WHILE ~(n IS Symbol) DO
      n := n. Last()
    END;
    RETURN n(Symbol)
  END LastSym;


PROCEDURE (nup: Node) Next* (n: Node): Node;
(* Returns the entity following `n' in `n. up', and NIL if `n' is the last
   part of `n. up'.  *)
  VAR
    lastSym, node: Node;
  BEGIN
    ASSERT (nup = n. up);
    IF (nup = NIL) OR (nup. Last() = n) THEN
      RETURN NIL
    ELSE
      lastSym := n;
      WHILE ~(lastSym IS Symbol) DO
        lastSym := lastSym. Last()
      END;
      node := lastSym(Symbol). NextSym();
      IF (node # NIL) THEN
        WHILE (node. up # nup) DO
          node := node. up
        END;
        ASSERT (node # n)
      END;
      RETURN node
    END
  END Next;

PROCEDURE (nup: Node) Prev* (n: Node): Node;
(* Analogous to `Next'.  *)
  VAR
    firstSym, node: Node;
  BEGIN
    ASSERT (nup = n. up);
    IF (nup = NIL) OR (nup. First() = n) THEN
      RETURN NIL
    ELSE
      firstSym := n;
      WHILE ~(firstSym IS Symbol) DO
        firstSym := firstSym. First()
      END;
      node := firstSym(Symbol). PrevSym();
      IF (node # NIL) THEN
        WHILE (node. up # nup) DO
          node := node. up
        END;
        ASSERT (node # n)
      END;
      RETURN node
    END
  END Prev;

PROCEDURE (n: Node) Remove*;
(* Removes everything that is part of node `n' from the syntax tree.  
   Afterwards the node `n' is wiped clean and all relevant symbols are gone 
   from the symbol list.
   CAUTION: The pointer from `n.up' to `n' is _not_ removed.  The caller has
   to do this _before_ calling `Remove', otherwise the AST will remain in an 
   illegal state.  *)
  VAR
    start, end, sym, next: Symbol;
    n0, n1: Node;
  BEGIN  (* pre: ~(n IS Symbol) *)
    start := n. FirstSym();
    end := n. LastSym();
    end := end. next;
    n. Clear;
    
    sym := start;
    WHILE (sym # end) DO
      next := sym. next;
      
      (* remove `sym' from list of symbols *)
      sym. prev. next := sym. next;
      IF (sym. next # NIL) THEN
        sym. next. prev := sym. prev
      END;
      
      (* clear all nodes towards the root of the tree that have not been
         cleared yet; this will stop at `n', which is already cleared *)
      IF (sym. up # NIL) THEN  (* ignore comments and pragmas *)
        n0 := sym;
        REPEAT
          n1 := n0. up;
          n0. Clear;
          n0 := n1
        UNTIL (n0. up = NIL)
      END;
      
      sym := next
    END
  END Remove;

PROCEDURE (n: Symbol) Remove*;
  BEGIN
    n. prev. next := n. next;
    IF (n. next # NIL) THEN
      n. next. prev := n. prev
    END;
    n. Clear
  END Remove;

PROCEDURE (n: Symbol) Insert* (new: Symbol);
(* Inserts symbol `new' after `n' into the list of symbols.
   pre: The field `new.up' must be set correctly, or be NIL if `new' is a
     comment, or if no syntax tree has been build for the symbol list.  *)
  BEGIN
    new. next := n. next;
    new. prev := n;
    n. next := new;
    IF (new. next # NIL) THEN
      new. next. prev := new
    END
  END Insert;


PROCEDURE (sym: Symbol) Length*(): LONGINT;
(* Returns the length of the string representation of `sym'.  *)
  BEGIN
    RETURN LEN (sym. str^)-1
  END Length;

PROCEDURE (start: StartSymbol) Line* (sym: Symbol): LONGINT;
(* Calculates the line number of source code position `sym.pos'.  Numbering
   starts at 1.  *)
  VAR
    l, r, m: LONGINT;
  BEGIN
    l := -1; r := start. lines;
    WHILE (l+1 # r) DO
      m := (l + r) DIV 2;
      IF (start. linePos[m] <= sym. pos) THEN
        l := m
      ELSE  (* (start. linePos[m] > sym. pos) *)
        r := m
      END
    END;
    RETURN l+1
  END Line;

PROCEDURE (n: Symbol) Clear*;
  BEGIN
    n. Clear^; n. next := NIL; n. prev := NIL; n. str := NIL
  END Clear;

PROCEDURE (n: Symbol) First*(): Node;
  BEGIN
    RETURN NIL
  END First;

PROCEDURE (n: Symbol) Last*(): Node;
  BEGIN
    RETURN NIL
  END Last;

PROCEDURE (sym: Symbol) NegatePos*;
(* Set `sym.pos' to `-sym.pos'.  Quite useful as a simple way to mark some
   symbols.  Note that any procedure changing the position information in
   this way is required to restore it to its original state!  *)
  BEGIN
    sym. pos := -sym.pos
  END NegatePos;

PROCEDURE (from: Symbol) CopyCoord* (to: Symbol; inclColumn: BOOLEAN);
  BEGIN
    IF (to # NIL) THEN
      to. line := from. line;
      IF inclColumn THEN
        to. column := from. column
      END
    END
  END CopyCoord;

PROCEDURE DocString* (sym: Symbol): BOOLEAN;
  BEGIN  (* re: "\(\*\*[ a-zA-Z]"
            whitespace is defined as in CharClass.IsWhiteSpace *)
    RETURN (sym. id = comment) & 
           (sym. str[2] = "*") &
           (CharClass.IsWhiteSpace (sym. str[3]) OR
            CharClass.IsLetter (sym. str[3]))
  END DocString;



PROCEDURE Err (msg: ARRAY OF CHAR);
  BEGIN
    Out.String ("In file ");
    Out.String (sourceFile^);
    Out.String (": ");
    Out.Ln;
    Out.LongInt (sym. pos, 0);
    Out.String (": ");
    Out.String (msg);
    Out.Ln;
    HALT (1)
  END Err;

PROCEDURE SynErr;
(* Signals a syntax error at the position of the current symbol, then aborts
   program.  *)
  BEGIN
    Err ("Syntax error")
  END SynErr;

PROCEDURE TypeErr;
(* Signals a type error at the position of the current symbol, then aborts
   program.  *)
  BEGIN
    Err ("Type error")
  END TypeErr;

PROCEDURE NotFound;
  BEGIN
    Err ("Undeclared identifier")
  END NotFound;

PROCEDURE AlreadyDefined;
  BEGIN
    Err ("This identifier is already defined")
  END AlreadyDefined;


PROCEDURE Msg* (msg: ARRAY OF CHAR);
(* Writes `msg' plus newline to stdout.  *)
  BEGIN
    Out.String (msg);
    Out.Ln;
    Out.Flush
  END Msg;

PROCEDURE InitSym (s: Symbol);
  BEGIN
    s. up := NIL;
    s. next := NIL; s. prev := NIL; 
    s. line := -1; s. column := -1;
    s. id := -1; s. str := NIL;
    WITH s: StartSymbol DO
      s. file := NIL;
      s. lines := -1;
      NEW (s. linePos, initLinePos);
      s. linePos[0] := 0
    | s: TextSymbol DO
      s. endLine := -1; s. endColumn := -1; s. info := NIL
    | s: NumberSymbol DO
      s. numType := -1; s. intVal := 0
    ELSE
    END
  END InitSym;

PROCEDURE NewSymbol* (str: ARRAY OF CHAR; line, col, pos: LONGINT): Symbol;
(* Creates new symbol of type `comment'.  The string must not contains any
   end of line characters or other control characters.  *)
  VAR
    t: TextSymbol;
    strPtr: String;
  BEGIN
    NEW (t);
    InitSym (t);
    t. id := comment;
    t. line := line;
    t. column := col;
    t. pos := pos;
    NEW (strPtr, Strings.Length (str)+1);
    COPY (str, strPtr^);
    t. str := strPtr;
    t. endLine := line;
    t. endColumn := col+LEN (strPtr^)-1;
    RETURN t
  END NewSymbol;



PROCEDURE ^ GetSym;

PROCEDURE CheckSym (s: SHORTINT);
(* If `s = sym', then get next symbol, otherwise signal a syntax error.  *)
  BEGIN
    IF (sym. id = s) THEN
      GetSym
    ELSE
      SynErr
    END
  END CheckSym;

PROCEDURE StoreString*(VAR buf: ARRAY OF CHAR; sym: Symbol; from, to: LONGINT);
(* Store the characters `buf[from..to-1]' in `sym.str^'.  Also update position
   of end of symbol in `sym'.  *)
  VAR
    h, i, j, len, sum, hash: LONGINT;
    str, hashed: String;
    strArray: StringArray;
  BEGIN
    sum := 0;
    FOR i := from TO to-1 DO
      INC (sum, ORD (buf[i]))
    END;
    
    hash := sum MOD sizeStringTable;
    i := 0; str := NIL;
    hashed := stringTable[hash][i];
    WHILE (hashed # NIL) & (str = NIL) DO
      j := 0; h := from;
      WHILE (hashed[j] # 0X) & (hashed[j] = buf[h]) DO
        INC (j); INC (h)
      END;
      IF (hashed[j] = 0X) & (h = to) THEN  (* found matching string *)
        str := hashed
      END;
      INC (i);
      hashed := stringTable[hash][i]
    END;
    IF (str = NIL) THEN  (* no matching string stored *)
      len := to-from;
      NEW (str, len+1);
      (* copy characters from file buffer into string buffer *)
      j := 0; h := from;
      WHILE (h # to) DO
        str[j] := buf[h]; INC (h); INC (j)
      END;
      str[j] := 0X;
      
      stringTable[hash][i] := str;
      h := LEN (stringTable[hash]^);
      IF (i = h-1) THEN
        NEW (strArray, h*2);
        FOR j := 0 TO h-1 DO
          strArray[j] := stringTable[hash][j]
        END;
        FOR j := h TO h*2-1 DO
          strArray[j] := NIL
        END;
        stringTable[hash] := strArray
      END
    END;

    sym. pos := from;
    sym. str := str;
    WITH sym: TextSymbol DO
      sym. endLine := currLine;
      sym. endColumn := pos-currLinePos+1
    ELSE
    END
  END StoreString;

PROCEDURE PopCond;
  BEGIN
    condStack := condStack. prev         (* remove top of stack *)
  END PopCond;

PROCEDURE ParsePragma;
(* Parses commands enclosed in <* .. *>.  *)

  CONST  
    tpUndef = 0;
    tpBoolean = 1;
    tpInteger = 2;
    tpString = 3;
    
  TYPE  
    Value = RECORD
      type: SHORTINT;
      boolean: BOOLEAN;
      integer: LONGINT;
      string: String;
      pos: LONGINT;
    END;
    
  VAR
    evalText, dummy, err, nested: BOOLEAN;
    ins: ARRAY 16 OF CHAR;
    s, s1: Symbol;
    start0, end0: LONGINT;
    text: TextSymbol;
    
  PROCEDURE CheckName (VAR name: ARRAY OF CHAR);
    BEGIN
      IF (name = "TRUE") OR (name = "FALSE") OR (name = "PUSH") OR 
         (name = "POP") OR (name = "DEFINE") THEN
        SynErr                           (* illegal variable name *)
      END
    END CheckName;
  
  PROCEDURE CheckBoolean (eval: BOOLEAN; VAR value: Value);
    BEGIN
      IF (value. type # tpBoolean) & (value. type # tpUndef) THEN
        IF eval THEN
          TypeErr                        (* boolean expression expected *)
        END;
        value. type := tpBoolean;
        value. boolean := FALSE
      END
    END CheckBoolean;
  
  PROCEDURE Expression (eval: BOOLEAN; VAR value: Value);
    VAR
      right: Value;
      pos0: LONGINT;
      op: SHORTINT;
      
    PROCEDURE SimpleExpr (eval: BOOLEAN; VAR value: Value);
      VAR
        right: Value;

      PROCEDURE Term (eval: BOOLEAN; VAR value: Value);
        VAR
          right: Value;
          
        PROCEDURE Factor (eval: BOOLEAN; VAR value: Value);
          VAR
            pragma: ParamPragmas.Pragma;
          BEGIN
            value. type := tpUndef;
            value. boolean := FALSE;
            value. integer := 0;
            value. string := NIL;
            value. pos := pos;
            IF (sym. id = ident) THEN
              IF (sym. str^ = "FALSE") OR 
                 (sym. str^ = "TRUE") THEN (* boolean const *)
                value. type := tpBoolean;
                value. boolean := (sym. str^ = "TRUE")
              ELSE                       (* variable *)
                CheckName (sym. str^);
                pragma := ParamPragmas.pragmas. Find (sym. str^);
                IF (pragma # NIL) THEN
                  WITH pragma: ParamOptions.BooleanOption DO
                    value. type := tpBoolean;
                    value. boolean := pragma. true
                  | pragma: ParamOptions.IntegerOption DO
                    value. type := tpInteger;
                    value. integer := pragma. value
                  | pragma: ParamOptions.StringOption DO
                    value. type := tpString;
                    value. string := pragma. value
                  END
                ELSIF eval THEN
                  NotFound               (* undeclared pragma variable *)
                END
              END;
              GetSym
            ELSIF (sym. id = number) & 
                  (sym(NumberSymbol). numType = numInt) THEN (* int const *)
              value. type := tpInteger;
              value. integer := sym(NumberSymbol). intVal;
              GetSym
            ELSIF (sym. id = string) THEN    (* string const *)
              value. type := tpString;
              NEW (value. string, Strings.Length (sym. str^)+1);
              COPY (sym. str^, value. string^);
              GetSym
            ELSIF (sym. id = lParen) THEN    (* parenthesis *)
              GetSym;
              Expression (eval, value);
              CheckSym (rParen)
            ELSIF (sym. id = not) THEN       (* negation *)
              GetSym;
              Expression (eval, value);
              CheckBoolean (eval, value);
              value. boolean := ~value. boolean
            ELSE
              SynErr;                    (* factor starts with illegal sym *)
              GetSym
            END
          END Factor;
        
        BEGIN
          Factor (eval, value);
          WHILE (sym. id = and) DO
            CheckBoolean (eval, value);
            value. pos := pos;
            GetSym;
            Factor (eval & value. boolean, right);
            CheckBoolean (eval & value. boolean, right);
            value. boolean := value. boolean & right. boolean
          END
        END Term;
      
      BEGIN
        Term (eval, value);
        WHILE (sym. id = or) DO
          CheckBoolean (eval, value);
          value. pos := pos;
          GetSym;
          Term (eval & ~value. boolean, right);
          CheckBoolean (eval & ~value. boolean, right);
          value. boolean := value. boolean OR right. boolean
        END
      END SimpleExpr;
    
    BEGIN
      SimpleExpr (eval, value);
      IF (eql <= sym. id) & (sym. id <= geq) THEN
        op := sym. id; pos0 := pos;
        GetSym;
        SimpleExpr (eval, right);
        IF ~eval OR (value. type = tpUndef) OR (right. type = tpUndef) THEN
          (* ignore *)
        ELSIF (value. type # right. type) THEN
           TypeErr                       (* operand incompatible to lhs *)
        ELSIF (value. type = tpBoolean) & 
              (lss <= sym. id) & (sym. id <= geq) THEN
           TypeErr                       (* operator not applicable to bool *)
        ELSIF eval THEN                  (* evaluate comparison *)
          CASE value. type OF
          | tpBoolean:
            CASE op OF
            | eql: value. boolean := (value. boolean = right. boolean)
            | neq: value. boolean := (value. boolean # right. boolean)
            END
          | tpInteger:
            CASE op OF
            | eql: value. boolean := (value. integer = right. integer)
            | neq: value. boolean := (value. integer # right. integer)
            | lss: value. boolean := (value. integer < right. integer)
            | leq: value. boolean := (value. integer <= right. integer)
            | gtr: value. boolean := (value. integer > right. integer)
            | geq: value. boolean := (value. integer >= right. integer)
            END
          | tpString:
            CASE op OF
            | eql: value. boolean := (value. string^ = right. string^)
            | neq: value. boolean := (value. string^ # right. string^)
            | lss: value. boolean := (value. string^ < right. string^)
            | leq: value. boolean := (value. string^ <= right. string^)
            | gtr: value. boolean := (value. string^ > right. string^)
            | geq: value. boolean := (value. string^ >= right. string^)
            END
          END
        END;
        value. pos := pos0;
        value. type := tpBoolean
      END
    END Expression;
  
  PROCEDURE BoolExpression (eval: BOOLEAN): BOOLEAN;
    VAR
      value: Value;
    BEGIN
      Expression (eval, value);
      CheckBoolean (eval, value);
      RETURN value. boolean
    END BoolExpression;
  
  PROCEDURE PushCond;
  (* Creates new stack element, pushes it onto `condStack' *)
    VAR
      cond: ConditionStack;
    BEGIN
      NEW (cond);
      cond. prev := condStack;
      cond. ifPos := pos;
      cond. skippedCond := ~evalText;
      cond. foundTrue := FALSE;
      cond. elsePresent := FALSE;
      condStack := cond
    END PushCond;
  
  PROCEDURE CheckForIf (noElse: BOOLEAN);
  (* Checks that an IF statement is opened.  If `noElse=TRUE', then it is also
     checked that no ELSE part is present.  *)
    BEGIN
      IF (condStack = NIL) THEN
        SynErr                           (* no open IF statement *)
      ELSIF noElse & condStack. elsePresent THEN
        SynErr                           (* ELSE part already declared *)
      END
    END CheckForIf;
  
  PROCEDURE Assignment (define, eval: BOOLEAN);
  (* define=TRUE: defining assignment, eval=TRUE: execute assignment *)
    VAR
      name: Param.LargeString;
      pragma: ParamPragmas.Pragma;
      value: Value;
    BEGIN
      IF (sym. id = ident) THEN
        IF eval THEN
          pragma := ParamPragmas.pragmas. Find (sym. str^);
          CheckName (sym. str^);
          COPY (sym. str^, name);
          IF (pragma = NIL) & ~define THEN
            NotFound                     (* undeclared pragma variable *)
          ELSIF (pragma # NIL) & define THEN
            AlreadyDefined               (* pragma variable already defined *)
          END;
          GetSym;
          CheckSym (becomes);
          Expression (eval, value);
          
          IF (value. type # tpUndef) THEN
            IF (pragma = NIL) THEN
              CASE value. type OF
              | tpBoolean: 
                pragma := ParamOptions.CreateBoolean (name, FALSE)
              | tpInteger: 
                pragma := ParamOptions.CreateInteger (name, 0, MIN (LONGINT), 
                                                               MAX (LONGINT))
              | tpString: 
                pragma := ParamOptions.CreateString (name, "")
              END;
              ParamPragmas.pragmas. Add (pragma)
            END;
            
            IF (pragma # NIL) THEN
              IF ~define THEN
                ParamPragmas.PrepareForModify (pragma)
              END;
              WITH pragma: ParamOptions.BooleanOption DO
                err := (value. type # tpBoolean);
                ins := "boolean";
                pragma. Set (value. boolean)
              | pragma: ParamOptions.IntegerOption DO
                err := (value. type # tpInteger);
                ins := "integer";
                pragma. Set (value. integer)
              | pragma: ParamOptions.StringOption DO
                err := (value. type # tpString);
                ins := "string";
                pragma. Set (value. string^)
              END;
              IF err THEN
                TypeErr                  (* not assignment compatible *)
              END
            END
          END
        ELSE  (* don't execute, just do syntax check *)
          GetSym;
          CheckSym (becomes);
          Expression (eval, value)
        END
      ELSE
        SynErr
      END
    END Assignment;
  
  BEGIN  (* pre: sym = "<*" *) 
    NEW (text);
    InitSym (text);
    text. line := sym. line; text. column := sym. column;
    sym := text;

    s := sym;
    s. id := pragma;
    start0 := pos-2;
    
    evalText := TRUE;
    REPEAT
      GetSym;
      scanStatus := inPragma;
      LOOP
        nested := (sym. id = if) OR (sym. id = elsif) OR (sym. id = else);
        IF (sym. id = if) OR (sym. id = elsif) THEN
          IF (sym. id = if) THEN
            PushCond
          ELSE  (* (sym = elsif) *)
            CheckForIf (TRUE)
          END;
          GetSym;
          IF condStack. skippedCond OR condStack. foundTrue THEN
            (* only do syntax check on guard *)
            dummy := BoolExpression (FALSE);
            evalText := FALSE
          ELSE                           (* evaluate guard *)
            condStack. foundTrue := BoolExpression (TRUE);
            evalText := condStack. foundTrue
          END;
          CheckSym (then)
        ELSIF (sym. id = else) THEN
          CheckForIf (TRUE);
          GetSym;
          evalText := ~condStack. skippedCond & ~condStack.foundTrue;
        ELSIF (sym. id = end) THEN
          CheckForIf (FALSE);
          evalText := ~condStack. skippedCond;
          PopCond;  (* remove top of stack *)
          GetSym
        ELSIF (sym. id = ident) & (sym. str^ = "DEFINE") THEN
          GetSym;
          Assignment (TRUE, evalText)
        ELSIF (sym. id = ident) & (sym. str^ = "PUSH") THEN
          IF evalText THEN ParamPragmas.Push END;
          GetSym
        ELSIF (sym. id = ident) & (sym. str^ = "POP") THEN
          IF evalText THEN
            IF (ParamPragmas.pragmas. stackLevel = 0) THEN
              SynErr                     (* pragma stack empty *)
            ELSE
              ParamPragmas.Pop
            END
          END;
          GetSym
        ELSIF (sym. id = ident) THEN
          Assignment (FALSE, evalText)
        END;
        IF (sym. id = semicolon) THEN
          GetSym
        ELSIF (sym. id # end) & ((sym. id = pragmaEnd) OR ~nested) THEN
          EXIT
        END
      END;
      scanStatus := skippingText;
      end0 := pos;
      IF evalText THEN
        s1 := sym;
        sym := s;
        StoreString (buf^, sym, start0, pos);
        sym := s1;
        IF (sym. id # pragmaEnd) THEN
          SynErr
        END
      ELSE
        CheckSym (pragmaEnd);
        (* skip Oberon-2 text inside conditional statement *)
        WHILE (sym. id # pragmaStart) & (sym. id # endOfFile) DO
          GetSym
        END
      END
    UNTIL (sym. id # pragmaStart);
    
    scanStatus := normal;
    sym := s
  END ParsePragma;

PROCEDURE CheckPragmas;
  BEGIN
    IF (condStack # NIL) THEN
      SynErr                             (* condition lacks END *)
    END
  END CheckPragmas;

PROCEDURE ReadBlock;
(* Reads part or all of the input buffer.  Aborts on read error.  *)
  VAR
    msg: ARRAY 1024 OF CHAR;
    read: LONGINT;
  BEGIN
    IF incrementalRead THEN
      IF (fileLen-currLen > sizeBlock) THEN
        read := sizeBlock
      ELSE
        read := fileLen-currLen
      END;
      inReader. ReadBytes (buf^, currLen, read);
      INC (currLen, read)
    ELSE
      inReader. ReadBytes (buf^, 0, fileLen);
      currLen := fileLen
    END;
    IF (inReader. res # Files.done) THEN
      msg := "Read error in file ";
      Strings.Append (sourceFile^, msg);
      Output.FatalError (msg)
    END
  END ReadBlock;


PROCEDURE NewLine;  (* pre: buf[pos] = eol *)
  VAR
    i: LONGINT;
    newPos: LinePos;
  BEGIN
    INC (pos);
    currLinePos := pos;
    currLineTab := 0;
    
    IF (currLine = LEN (startSymbol. linePos^)) THEN
      NEW (newPos, currLine+incrLinePos);
      FOR i := 0 TO currLine-1 DO
        newPos[i] := startSymbol. linePos[i]
      END;
      startSymbol. linePos := newPos
    END;
    startSymbol. linePos[currLine] := pos;
    
    INC (currLine)
  END NewLine;


PROCEDURE Comment;
(* Read comment.  This may include nested comments.
   pre: scan[pos]="*", scan[pos-1]="("  *)
  VAR
    start, level: LONGINT;
    text: TextSymbol;
  BEGIN
    NEW (text);
    InitSym (text);
    text. line := sym. line; text. column := sym. column;
    sym := text;
    
    sym. id := comment;
    start := pos-1;
    INC (pos);
    level := 1;
    LOOP  (* loop until end of comment/file reached *)
      IF incrementalRead & (currLen # fileLen) & (currLen-pos < sizeBlock DIV 2) THEN
        ReadBlock
      END;
      CASE buf[pos] OF
      | eof:                             (* end of file? *)
        IF (pos = fileLen) THEN
          SynErr                         (* comment not terminated *)
        ELSE
          INC (pos)
        END
      | CharClass.eol:
        NewLine
      | "*":
        INC (pos);
        IF (buf[pos] = ")") THEN         (* end of comment *)
          INC (pos);
          DEC (level);
          IF (level = 0) THEN
            EXIT
          END
        END
      | "(":
        INC (pos);
        IF (buf[pos] = "*") THEN         (* nested comments *)
          INC (level)
        END
      ELSE                               (* skip characters in comment *)
        INC (pos)
      END
    END;
    StoreString (buf^, sym, start, pos)
  END Comment;

PROCEDURE GetString (end: CHAR);
(* Read string with double or single quote as delimiter.  *)
  VAR
    start: LONGINT;
  BEGIN
    sym. id := string;
    start := pos;
    LOOP  (* loop until end or eof reached *)
      INC (pos);
      IF (buf[pos] < " ") THEN           (* illegal control character or eof *)
        SynErr  (* string not terminated or contains illegal char *)
      ELSIF (buf[pos] = end) THEN        (* end of string *)
        INC (pos); EXIT
      END
    END;
    StoreString (buf^, sym, start, pos)
  END GetString;

PROCEDURE Ident;
(* Reads identifiers and keywords.
   pre: `buf[pos]' is a character
   post: `buf[pos]' isn't a character or a cypher, `sym' is set to ident or
     to the corresponding keyword, a copy of the identifier is stored in 
     `str'. *)
  VAR
    start, sum, i: LONGINT;
    
  PROCEDURE CompareIdent (VAR kw: ARRAY OF CHAR): BOOLEAN;
  (* Compares the current identifier symbol starting at buffer position 
     `start' with `kw', returns TRUE if they are identical. *)
    VAR
      i: SHORTINT;
    BEGIN
      i := 0;
      WHILE (kw[i] # 0X) & (kw[i] = buf[start+i]) DO
        INC (i)
      END;
      RETURN (kw[i] = 0X) & (start+i = pos)
    END CompareIdent;
  
  PROCEDURE IsChar (inclDigit: BOOLEAN): BOOLEAN;
    BEGIN
      RETURN ("A" <= CAP (buf[pos])) & (CAP (buf[pos]) <= "Z") OR
             inclDigit & ("0" <= buf[pos]) & (buf[pos] <= "9") OR
             (buf[pos] = "_")
    END IsChar;
  
  PROCEDURE SkipWord;
    BEGIN
      REPEAT  (* loop to the first non char/cypher *)
        INC (sum, LONG (ORD (buf[pos])));
        INC (pos)
      UNTIL ~IsChar (TRUE)
    END SkipWord;
  
  BEGIN
    sym. id := ident; sum := 0; start := pos;
    IF moduleIdent THEN
      SkipWord;
      WHILE (buf[pos] = moduleSeparator) & (buf[pos+1] # "=") DO
        INC (pos);
        IF IsChar(FALSE) THEN
          SkipWord
        END
      END
    ELSE
      REPEAT  (* loop to the first non char/cypher *)
        INC (sum, LONG (ORD (buf[pos])));
        INC (pos)
      UNTIL ~ (("A" <= CAP (buf[pos])) & (CAP (buf[pos]) <= "Z") OR
               ("0" <= buf[pos]) & (buf[pos] <= "9") OR
               (buf[pos] = "_"))
    END;
    StoreString (buf^, sym, start, pos);
    
    (* compare identifier against list of keywords; 
       modify `sym' if it matches one of them *)
    i := sum MOD sizeKWTable;
    IF (kwSym[i, 0] >= 0) THEN
      IF CompareIdent (kwStr[i, 0]^) THEN
        sym. id := kwSym[i, 0]
      ELSIF (kwSym[i, 1] >= 0) & CompareIdent (kwStr[i, 1]^) THEN
        sym. id := kwSym[i, 1]
      END
    END
  END Ident;

PROCEDURE Number;
(* Parses and converts numbers.  *)
  VAR
    format: SHORTINT;
    start, i: LONGINT;
    num: NumberSymbol;

  PROCEDURE ConvertHex(spos, epos: LONGINT): LONGINT;
    VAR
      result: LONGINT;
      
    PROCEDURE GetCypher(c: CHAR): INTEGER;
      VAR
        d: INTEGER;
      BEGIN
        d:=ORD(c);
        IF (ORD ("0") <= d) & (d <= ORD ("9")) THEN
          DEC (d, ORD ("0"))
        ELSE  (* (ORD ("A") <= d) & (d <= ORD ("F")) *)
          (* the explicit test can be omitted, since this procedure is only 
             called for numbers with H or X suffix, and the initial REPEAT 
             loop in `Number' only accepts valid hexadecimal digits from 
             the ranges "0".."9" and "A".."F" *)
          DEC (d, ORD ("A")-10)
        END;
        RETURN d
      END GetCypher;
    
    BEGIN
      result := 0;
      (* skip leading zeros *)
      WHILE (buf[spos] = "0") DO 
        INC (spos)
      END;
      IF (epos-spos > 7) THEN  (* value has more than 8 significant cyphers *)
        TypeErr                          (* number out of range *)
      ELSIF (spos <= epos) THEN         (* if any non-zero cyphers follow *)
        result := GetCypher (buf[spos]);
        INC (spos);
        IF (epos-spos = 6) & (result >= 8) THEN
          (* value is beyond MAX(LONGINT)=07FFFFFFFH: correct this by sub-
             tracting 16 from the value of the most significant digit, creating
             the negative number that matches the bit pattern *)
          DEC (result, 10H)
        END;
        WHILE (spos <= epos) DO
          result := result*10H + GetCypher (buf[spos]);
          INC (spos)
        END
      (* ELSE: number is non-empty sequence of "0", keep result=0 *)
      END;
      RETURN result
    END ConvertHex;

  BEGIN
    NEW (num);
    InitSym (num);
    num. line := sym. line; num. column := sym. column;
    num. id := number; 
    start := pos;
    (* scan characters til the first non (hex-) cypher; note: lower case 
       characters like "a" are _not_ valid hex digits *)
    REPEAT
      INC (pos)
    UNTIL ~ (("0" <= buf[pos]) & (buf[pos] <= "9") OR 
             ("A" <= buf[pos]) & (buf[pos] <= "F"));
             
    IF (buf[pos] = ".") & (buf[pos+1] # ".") THEN  
      (* real (but not a `..' token) *)
      INC (pos);
      (* read decimal fraction *)
      WHILE ("0" <= buf[pos]) & (buf[pos] <= "9") DO
        INC (pos)
      END;
      (* determine constant type (long real, or just real?) *)
      IF (buf[pos] = "D") THEN
        num. numType := numLReal; buf[pos] := "E"
      ELSE
        num. numType := numReal
      END;
      IF (buf[pos] = "E") THEN  (* read scale factor *)
        INC (pos);
        IF (buf[pos] = "-") OR (buf[pos] = "+") THEN
          INC (pos)
        END;
        IF ("0" <= buf[pos]) & (buf[pos] <= "9") THEN
          REPEAT
            INC (pos)
          UNTIL (buf[pos] < "0") OR ("9" < buf[pos])
        ELSE
          SynErr                         (* illegal exponent format *)
        END
      END;
      StoreString (buf^, sym, start, pos)
    ELSE  (* integer *)
      num. intVal := 0;
      (* determine base of representation *)
      IF (buf[pos] = "H") OR (buf[pos] = "X") THEN
        num. intVal := ConvertHex (start, pos-1);
      ELSE
        (* check whether all characters are decimal digits *)
        i := start;
        WHILE (i # pos) & ("0" <= buf[i]) & (buf[i] <= "9") DO
          INC (i)
        END;
        IF (i # pos) THEN                (* buf[i] isn't from "0".."9" *)
          num. intVal := 1; SynErr       (* illegal cypher *)
        ELSE
          StoreString (buf^, num, start, pos);
          IntStr.StrToInt (num. str^, num. intVal, format);
          IF (format = IntStr.strOutOfRange) THEN
            SynErr                       (* number out of range *)
          END
        END
      END;
      (* set constant type according to suffix *)
      IF (buf[pos] = "X") THEN
        num. id := string; INC (pos)
      ELSE
        IF (buf[pos] = "H") THEN INC (pos) END;
        num. numType := numInt
      END
    END;
    sym := num
  END Number;

PROCEDURE NewSym (): Symbol;
  VAR
    s: Symbol;
  BEGIN
    NEW (s);
    InitSym (s);
    RETURN s
  END NewSym;


PROCEDURE GetSym;
(* Reads next token.  The symbol description is stored in `sym'.  *)
  VAR
    start, currColumn: LONGINT;
  BEGIN
    IF incrementalRead & (currLen#fileLen) & (currLen-pos < sizeBlock DIV 2) THEN
      ReadBlock
    END;
    
    (* skip whitespace characters *)
    sym := NewSym();
    WHILE (buf[pos] <= " ") DO
      IF (buf[pos] = eof) & (pos = fileLen) THEN
        sym. id := endOfFile;
        RETURN
      ELSIF (buf[pos] = CharClass.eol) THEN
        NewLine
      ELSIF (buf[pos] = Ascii.ht) THEN  (* adjust for horizontal tabulator *)
        currColumn := pos-currLinePos+currLineTab;
        INC (currLineTab, tabWidth-currColumn MOD tabWidth-1);
        INC (pos)
      ELSE
        INC (pos)
      END
    END;
    
    start := pos;
    sym. line := currLine;
    sym. column := pos-currLinePos+currLineTab+1;
    
    CASE buf[pos] OF
    | "a".."z", "A".."Z", "_": Ident
    | "0".."9": Number
    | '"', "'": GetString (buf[pos])
    | "~": sym. id := not; INC (pos)
    | "{": sym. id := lBrace; INC (pos)
    | ".": 
      INC (pos);
      IF (buf[pos] = ".") THEN 
        sym. id := upto; 
        INC (pos);
        IF (buf[pos] = ".") THEN 
          sym. id := threeDots;
          INC (pos)
        END
      ELSE 
        sym. id := period
      END
    | "^": sym. id := arrow; INC (pos)
    | "[": sym. id := lBrak; INC (pos)
    | ":": 
      INC (pos);
      IF (buf[pos] = "=") THEN 
        sym. id := becomes; INC (pos)
      ELSE 
        sym. id := colon
      END
    | "(": 
      INC (pos);
      IF (buf[pos] = "*") THEN 
        Comment
      ELSE 
        sym. id := lParen
      END
    | "*": 
      sym. id := times; INC (pos);
      IF (buf[pos] = ")") THEN
        SynErr;                          (* no comment started *)
        INC (pos)
      ELSIF (buf[pos] = ">") THEN
        IF (scanStatus = inPragma) THEN
          sym. id := pragmaEnd; INC (pos)
        ELSE
          SynErr                         (* no <* opened *)
        END
      END
    | "/": sym. id := slash; INC (pos)
    | "&": sym. id := and; INC (pos)
    | "+": sym. id := plus; INC (pos)
    | "-": sym. id := minus; INC (pos)
    | "=": sym. id := eql; INC (pos)
    | "#": sym. id := neq; INC (pos)
    | "<": 
      INC (pos);
      IF (buf[pos] = "=") THEN 
        sym. id := leq; INC (pos)
      ELSIF (buf[pos] = "*") THEN
        IF (scanStatus = inPragma) THEN
          SynErr                         (* nested <* *)
        ELSIF (scanStatus = skippingText) THEN
          sym. id := pragmaStart; INC (pos)
        ELSE  (* (scanStatus = normal) *)
          INC (pos);
          ParsePragma
        END
      ELSE 
        sym. id := lss 
      END
    | ">": 
      INC (pos);
      IF (buf[pos] = "=") THEN 
        sym. id := geq; INC (pos)
      ELSE 
        sym. id := gtr
      END
    | "}": sym. id := rBrace; INC (pos)
    | ")": sym. id := rParen; INC (pos)
    | "]": sym. id := rBrak; INC (pos)
    | "|": sym. id := bar; INC (pos)
    | ";": sym. id := semicolon; INC (pos)
    | ",": sym. id := comma; INC (pos)
    ELSE
      SynErr                             (* illegal symbol *)
    END;
    
    IF (sym. str = NIL) THEN
      StoreString (buf^, sym, start, pos)
    END
  END GetSym;


PROCEDURE Init (fileName: ARRAY OF CHAR; incrRead: BOOLEAN): StartSymbol;
(* Reads contents of file `fileName' into the internal buffer.  If `fileName'
   matches an RCS file name, the file is checked out first, and the contents
   of the working file are read.  The name of the file is stored in 
   `E.sourceFile' (it differs from `fileName' in the case of RCS files).  On
   success the first token is read by calling `GetSym'.  A failure to open or
   to read the file will abort the program by calling `Output.FatalError'.  
   `incrRead=TRUE' enables incremental reading.  This means that, instead of 
   reading the whole file at once, only chunks of `sizeBlock' bytes are read 
   on demand.  This should only be used for the Make utility, since it limits
   the maximum length of strings and identifiers to `sizeBlock DIV 2', and an
   overflow is not detected.  *)
  CONST
    firstBuffer = 32*1024-16;            
    (* initial size of file buffer; make sure that buffer+tag fit closely 
       into a block of 2^n bytes *)
    incrBuffer = 16*1024;
    (* step by which the buffer size is incremented if the current buffer 
       isn't large enough to hold the next file; should be some 2^n *)
  VAR
    i: LONGINT;
    res: Files.Result;
    msg: ARRAY 1024 OF CHAR;
    start: StartSymbol;
  BEGIN
    incrementalRead := incrRead;
    IF ParamPaths.paths. rcsEnabled & VC.MasterFile (fileName) THEN
      IF VC.CheckOut (fileName, msg) THEN
        Msg (msg)  (* success, write checkout command if --verbose *)
      ELSE  (* failure, abort with error message *)
        Output.FatalError (msg)
      END
    END;

    inFile := Files.Old (fileName, {Files.read}, res);
    NEW (sourceFile, Strings.Length (fileName)+1);
    COPY (fileName, sourceFile^);        (* store file name actually used *)
    IF (inFile = NIL) THEN
      msg := "File ";
      Strings.Append (fileName, msg);
      Strings.Append (" not found", msg);
      Output.FatalError (msg)
    ELSE
      fileLen := inFile. Length();
      (* allocate buffer *)
      IF (buf = NIL) OR (LEN(buf^) < fileLen+1) THEN
        IF (buf = NIL) THEN
          i := firstBuffer
        ELSE
          i := LEN(buf^)
        END;
        WHILE (i <= fileLen+1) DO     (* increase buffer size if necessary *)
          INC (i, incrBuffer)
        END;
        NEW (buf, i)
      END;

      buf[fileLen] := eof; currLen := 0; pos := 0; 
      condStack := NIL; scanStatus := normal;
      currLine := 1; currLinePos := 0; currLineTab := 0;

      (* read file *)
      inReader := inFile. NewReader();
      ReadBlock
    END;
    
    NEW (start);
    InitSym (start);
    start. file := sourceFile;
    start. pos := 0; start. line := 1; start. column := 1;
    startSymbol := start; moduleIdent := FALSE;
    RETURN start
  END Init;

PROCEDURE Close;
  BEGIN
    IF (inFile # NIL) THEN
      inFile. Close;
      inFile := NIL
    END;
    startSymbol := NIL;
    sym := NIL
  END Close;

PROCEDURE ScanFile* (fileName: ARRAY OF CHAR): StartSymbol;
(* Reads file `fileName' and turns it into a symbol list.  The first element
   of the list is a pseudo symbol holding information about the file being
   parsed (like file name and number of lines).  Any error while scanning the
   module text will abort the program.  *)
  VAR
    last: Symbol;
    start: StartSymbol;
  BEGIN
    Output.VerboseMsg ("- ", fileName);
    start := Init (fileName, FALSE);
    last := start;
    GetSym;                             (* initialize token stream *)
    IF (sym. id = endOfFile) THEN sym := NIL END;
    moduleIdent := TRUE;
    WHILE (sym # NIL) DO
      sym. prev := last;
      sym. next := NIL;
      last. next := sym;
      last := sym;
      
      IF moduleIdent & (const <= last. id) & (last. id <= procedure) THEN
        (* disable extended names after IMPORT statment *)
        moduleIdent := FALSE
      END;
      
      IF ~moduleIdent & (last. id = end) THEN
        (* enable extended names for symbols following END to handle the
           trailing module name *)
        moduleIdent := TRUE;
        GetSym;
        moduleIdent := FALSE
      ELSE
        GetSym
      END;
      IF (sym. id = endOfFile) THEN sym := NIL END
    END;
    CheckPragmas;
    start. lines := currLine;
    Close;
    
    ParamPragmas.Restore (pragmas);
    
    RETURN start
  END ScanFile;

PROCEDURE ScanImports* (fileName: ARRAY OF CHAR): Symbol;
(* Reads the import list of module `fileName' and returns the module name 
   itself followed by the names of all imported modules.  Result is just the
   module name if there is no import statement.  Alias names are discarded.  
   Any error while scanning the module text will abort the program.  *)
  VAR
    mod, dummy: Symbol;
    
  PROCEDURE NextSym;
    BEGIN
      REPEAT
        GetSym
      UNTIL (sym. id # comment) & (sym. id # pragma)
    END NextSym;
  
  PROCEDURE CheckSym (id: SHORTINT);
    BEGIN
      IF (sym. id # id) THEN
        SynErr
      ELSE
        NextSym
      END
    END CheckSym;
    
  PROCEDURE ImportList (): Symbol;
    VAR
      mod, start, last: Symbol;
    BEGIN
      start := NIL;
      LOOP
        IF (sym. id = ident) THEN
          mod := sym;
          NextSym;
          IF (sym. id = becomes) THEN
            NextSym;
            IF (sym. id = ident) THEN
              mod := sym;
              NextSym
            ELSE
              SynErr
            END
          END;
          IF (start = NIL) THEN
            start := mod
          ELSE
            mod. prev := last;
            last. next := mod
          END;
          last := mod
        ELSE
          SynErr
        END;
        IF (sym. id # comma) THEN
          EXIT
        END;
        NextSym
      END;
      CheckSym (semicolon);
      RETURN start
    END ImportList;
  
  BEGIN
    dummy := Init (fileName, TRUE);
    NextSym;                             (* initialize token stream *)

    moduleIdent := TRUE;
    CheckSym (module);
    moduleIdent := FALSE;
    mod := sym;
    CheckSym (ident);
    IF (sym. id = lBrak) THEN
      WHILE (sym. id # rBrak) & (sym. id # endOfFile) DO
        NextSym
      END;
      IF (sym. id = rBrak) THEN
        NextSym
      END
    END;
    CheckSym (semicolon);
    
    IF (sym. id = import) THEN
      moduleIdent := TRUE;
      NextSym;
      mod. next := ImportList();
      moduleIdent := FALSE;
      IF (mod. next # NIL) THEN
        mod. next. prev := mod
      END
    END;
    
    Close;
    ParamPragmas.Restore (pragmas);
    
    RETURN mod
  END ScanImports;



PROCEDURE Abs2Rel* (list: StartSymbol);
(* Convert absolute coordinates in symbol list `list' into relative 
   coordinates.  That is, replace (line, column) pairs with (line offset, 
   column offset) pair.   The first symbol will have the coordinates (0, 0),
   and for every following symbol the coordinates tell how many lines and 
   spaces have to be inserted after the end of the preceding symbol.  (0, y)
   means insert `y' spaces, while (x, y) means insert `x' lines and indent for
   `y' characters.  *)
  VAR
    sym: Symbol;
    prevLine, prevColumn, endLine, endColumn: LONGINT;
  BEGIN
    sym := list. next;
    IF (sym # NIL) THEN
      prevLine := sym. line;
      prevColumn := sym. column;
      WHILE (sym # NIL) DO
        (* where does the current symbol end? *)
        WITH sym: TextSymbol DO
          endLine := sym. endLine;
          endColumn := sym. endColumn
        ELSE
          endLine := sym. line;
          endColumn := sym. column + sym. Length()
        END;
        (* adjust coordinates *)
        DEC (sym. line, prevLine);
        IF (sym. line = 0) THEN
          DEC (sym. column, prevColumn)
        ELSE
          DEC (sym. column)
        END;
        prevLine := endLine;
        prevColumn := endColumn;
        sym := sym. next
      END
    END
  END Abs2Rel;

PROCEDURE RemoveComments* (startSymbol: StartSymbol);
(* Removes all comments and pragmas from the symbol list.  *)
  VAR
    sym, next: Symbol;
  BEGIN
    sym := startSymbol. next;
    WHILE (sym # NIL) DO
      next := sym. next;
      IF (sym. id >= comment) THEN
        sym. prev. next := sym. next;
        IF (sym. next # NIL) THEN
          sym. next. prev := sym. prev
        END;
        sym. Clear
      END;
      sym := next
    END
  END RemoveComments;

PROCEDURE RemoveUnusedSymbols* (startSymbol: StartSymbol);
(* Removes all symbols from the list that have an `up' pointer of NIL.
   Note: This includes all comments and pragmas.  *)
  VAR
    sym, next: Symbol;
  BEGIN
    sym := startSymbol. next;
    WHILE (sym # NIL) DO
      next := sym. next;
      IF (sym.  up = NIL) THEN
        sym. prev. next := sym. next;
        IF (sym. next # NIL) THEN
          sym. next. prev := sym. prev
        END;
        sym. Clear
      END;
      sym := next
    END
  END RemoveUnusedSymbols;

PROCEDURE ClearStringTable*;
(* Remove all entries from table of hashed strings.  Should be done after a
   module has been scanned.  *)
  VAR
    i, j: LONGINT;
  BEGIN
    FOR i := 0 TO sizeStringTable-1 DO
      j := 0;
      WHILE (stringTable[i][j] # NIL) DO
        stringTable[i][j] := NIL;
        INC (j)
      END
    END
  END ClearStringTable;


PROCEDURE String2Comment* (file: ARRAY OF CHAR; s: String): TextSymbol;
(* Debug function.  Takes a plain string "foo", and creates a comment symbol
   with the content "(*foo*)" for the file name `file'.  *)
  VAR
    start: StartSymbol;
    text: TextSymbol;
  BEGIN
    NEW (start);
    InitSym (start);
    NEW (start. file, Strings.Length (file)+1);
    COPY (file, start. file^);
    start. pos := 0; start. line := 1; start. column := 1;
    
    NEW (text);
    InitSym (text);
    NEW (text. str, Strings.Length (s^)+5);
    COPY (s^, text. str^);
    Strings.Insert ("(*", 0, text. str^);
    Strings.Append ("*)", text. str^);
    text. pos := 0; text. line := 1; text. column := 1;
    text. prev := start;
    start. next := text;
    
    RETURN text
  END String2Comment;

PROCEDURE InitKeywords;
(* Fills hash table used by `Ident' to identify the keywords. *)
  VAR
    i, j: LONGINT;

  PROCEDURE KW (ident: ARRAY OF CHAR; sym: SHORTINT);
    VAR
      h, i, j, sum: INTEGER;
      str: String;
    BEGIN
      sum := 0; i := 0;
      WHILE (ident[i] # 0X) DO
        INC (sum, ORD (ident[i])); INC (i)
      END;
      j := sum MOD sizeKWTable;
      NEW (str, i+1);
      COPY (ident, str^);
      IF (kwSym[j, 0] < 0) THEN
        kwSym[j, 0] := sym;
        kwStr[j, 0] := str
      ELSE
        kwSym[j, 1] := sym;
        kwStr[j, 1] := str
      END;
      
      h := 0;
      WHILE (stringTable[sum MOD sizeStringTable][h] # NIL) DO
        INC (h)
      END;
      stringTable[sum MOD sizeStringTable][h] := str
    END KW;

  BEGIN
    FOR i := 0 TO sizeKWTable-1 DO
      kwSym[i, 0] := -1; kwSym[i, 1] := -1;
      kwStr[i, 0] := NIL; kwStr[i, 1] := NIL
    END;
    FOR i := 0 TO sizeStringTable-1 DO
      NEW (stringTable[i], 8);
      FOR j := 0 TO LEN (stringTable[i]^)-1 DO
        stringTable[i][j] := NIL
      END
    END;
    
    KW ("ARRAY", array); KW ("BEGIN", begin); KW ("BY", by); KW ("CASE", case);
    KW ("CONST", const); KW ("DIV", div); KW ("DO", do); KW ("ELSE", else);
    KW ("ELSIF", elsif); KW ("END", end); KW ("EXIT", exit); KW ("FOR", for);
    KW ("IF", if); KW ("IMPORT", import); KW ("IN", in); KW ("IS", is);
    KW ("LOOP", loop); KW ("MOD", mod); KW ("MODULE", module); KW ("NIL", nil);
    KW ("OF", of); KW ("OR", or); KW ("POINTER", pointer); 
    KW ("PROCEDURE", procedure); KW ("RECORD", record); KW ("REPEAT", repeat);
    KW ("RETURN", return); KW ("THEN", then); KW ("TO", to); KW ("TYPE", type);
    KW ("UNTIL", until); KW ("VAR", var); KW ("WHILE", while); 
    KW ("WITH", with)
  END InitKeywords;

BEGIN
  buf := NIL; inFile := NIL; inReader := NIL; 
  sourceFile := NIL; startSymbol := NIL; moduleIdent := FALSE;
  NEW (undefSym); InitSym (undefSym);
  InitKeywords
END CNScanner.
