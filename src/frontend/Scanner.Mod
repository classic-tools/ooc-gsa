(* 	$Id: Scanner.Mod,v 1.41 2000/03/01 09:45:33 ooc-devel Exp $	 *)
MODULE Scanner;
(*  Lexical scanner for Oberon-2 source code.
    Copyright (C) 1995-2000  Michael van Acken

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
  Termination, Channel, Files, IntStr, RealStr, LRealStr, Strings, 
  Param := Parameter, ParamOptions, ParamPaths, ParamPragmas,
  Config, Data, StdTypes, E := Error, VC := RCS;


VAR
  stringLength-: ParamOptions.IntegerOption;
  (* this pragma variable determines the maximum number of characters in a 
     string before the scanner barfs; a value of n<0 will produce a warning, 
     n>0 will produce an error if `Strings.Length(string) > ABS(n)'; 
     n=MIN(LONGINT) disables any length restrictions *)
  identLength-: ParamOptions.IntegerOption;
  (* this pragma variable determines the maximum number of characters in an 
     identifier before the scanner barfs; a value of n<0 will produce a 
     warning, n>0 will produce an error if `Strings.Length(ident) > ABS(n)'; 
     n=MIN(LONGINT) disables any length restrictions *)
  allowUnderscore*: BOOLEAN;
  (* if TRUE, then identifiers can contain an underscore in place of a letter;
     most of the time the value corresponds to the `objAllowsUnderscore' flag
     of the current module, although it may change when selecting an imported 
     declaration or a record field *)
  moduleIdent*: BOOLEAN;
  (* if TRUE, then identifiers can contain the character `moduleSeparator';
     if \c designates a character, \w a character or a digit, and ":" the 
     separator, a module identifier must satisfy the regular expression 
     "\c\w* ( :\c\w* )*" *)
     
  
CONST
  undefStr* = "???";

  moduleSeparator* = ":";
  (* with `moduleIdent=TRUE', identifiers can contain this character; this
     means that an identifier can look like "foo:bar:M"; illegal variants
     (like ":foo", "foo:", or "foo::bar") are detected by the scanner and
     marked as faulty *)
     
  eof = 00X;                             
  (* end of file marker, always appended to the buffer by `Init' *)
  eol = 0AX;
  (* end of line code *)
  sizeKWTable = 128;                     
  (* size of keyword hash table *)
  sizeBlock = 2*1024;
  (* number of bytes read per chunk if `incrementalRead' is TRUE *)
  
  (* kinds of tokens returned by `GetSym' in variable `sym' *)
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
  (* symbols `<*' and `*>', internal use only *)
  pragmaStart=65; pragmaEnd=66;

  (* return values for `numType', set by `GetSym' *)
  numInt*=1; numReal*=2; numLReal*=3;

VAR
  kwStr: ARRAY sizeKWTable, 2, 10 OF CHAR; 
  (* hash table for keywords, used bz `Ident' *)
  kwSym: ARRAY sizeKWTable, 2 OF SHORTINT; 
  (* token for associated keywords (values for `sym') *)

  incrementalRead: BOOLEAN;
  (* read files in chunks of `sizeBlock' bytes (used for make to scan sources
     without having to read all of the file) *)
  buf: POINTER TO ARRAY OF CHAR;         
  (* buffer area, used to hold the whole file *)
  pos: LONGINT;                          
  (* current scanning position in `buf' *)
  fileLen: LONGINT;
  (* length of input file in bytes *)
  currLen: LONGINT;
  (* number of bytes that have been read from the file; until the end of the 
     file is reached, the relation `currLen-pos >= sizeBlock DIV 2' holds with
     every call of `GetSym' *)
  inFile: Files.File;
  inReader: Channel.Reader;
  (* file and rider on input file *)
  
  (* All of the following variables are set by `GetSym' to return the current
     symbol and its attribute values: *)
  sym-: SHORTINT;                        
  (* current token *)
  currSymPos-: LONGINT;                     
  (* file position of current token *)
  lastSymEnd-: LONGINT;
  (* file position of end of last parsed token *)
  str-: Data.String;                       
  (* space to return string and identifier values; always use copies of `str^'
     in data structures, rather than simply copying the pointer itself *)
  numType-: SHORTINT;                    (* numInt, numReal or numLReal *)
  intVal-: LONGINT;
  realVal-: LONGREAL;
  (* those vars hold numerical attributes (when `sym=number') *)

  finished: BOOLEAN;
  (* FALSE while the source file is being parsed; used in `CatchSignal' *)

  sourceTotal*, sourceLines*: LONGINT;
  (* the number of characters and lines scanned; input read with 
     incrementalRead=TRUE is ignored *)
     
  
TYPE
  PosArray = POINTER TO ARRAY OF LONGINT;

VAR
  (* this array holds the file positions of all end of line characters; used
     by `Line' and `Col' to translate file position into line/column pair *)
  eolArray: PosArray;
  eolCounter: LONGINT;
  
(* see file `doc/Pragmas' for the specification of pragmas and conditional 
   compilation *)
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

TYPE  (* used by SaveScanPos/RestoreScanPos *)
  ScanState* = RECORD
    pos: LONGINT;
    condStack: ConditionStack;
    pragmaState: ParamPragmas.PragmaState;
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
  


PROCEDURE EndOfLine;
(* Adds end of line position to `eolArray'.  This information is used by
   `FindLine' to reconstruct the line number of a given file position. 
   pre: buf[pos] = eol *)
  VAR
    i: LONGINT;
    new: PosArray;
  BEGIN
    IF (eolCounter = LEN (eolArray^)) THEN
      NEW (new, (eolCounter+4)*2-4);
      FOR i := 0 TO eolCounter-1 DO
        new[i] := eolArray[i]
      END;
      eolArray := new
    END;
    eolArray[eolCounter] := pos;
    INC (eolCounter)
  END EndOfLine;

PROCEDURE FindLine (pos: LONGINT): LONGINT;
(* Calculates the line number of source code position `pos'.  Result is -1 for
   `pos < 0'.  *)
  VAR
    l, r, m: LONGINT;
  BEGIN
    IF (pos < 0) THEN
      RETURN -1
    ELSE
      l := -1; r := eolCounter;
      WHILE (l+1 # r) DO
        m := (l + r) DIV 2;
        IF (pos >= eolArray[m]) THEN
          l := m
        ELSE
          r := m
        END
      END;
      RETURN l
    END
  END FindLine;

PROCEDURE Line* (pos: LONGINT): LONGINT;
(* Returns the number of the source line that contains `pos'.  The first line 
   is 1.  The position of the `eol' character that terminates a line is
   considered as part of this line.  Result is 0 for `pos < 0'.  Note that 
   `pos' has to refer to the most recently parsed file, otherwise the result
   is undefined.  *)
  BEGIN
    RETURN FindLine (pos)+1
  END Line;

PROCEDURE Column* (pos: LONGINT): LONGINT;
(* Returns column number of `pos' in `Line(pos)'.  The left-most column is 1.
   Result is 0 for `pos < 0' .  Note that `pos' has to refer to the most 
   recently parsed file, otherwise the result is undefined.  *)
  VAR
    line: LONGINT;
  BEGIN
    line := FindLine (pos);
    IF (line <= 0) THEN
      IF (pos < 0) THEN
        RETURN 0
      ELSE
        RETURN pos+1
      END
    ELSE
      RETURN pos-1-eolArray[line-1]+1
    END
  END Column;


PROCEDURE ^ GetSym*;

PROCEDURE CheckSym* (s: SHORTINT);
(* If `s = sym', then get next symbol, otherwise signal error and call
   `GetSym' to skip the this symbol for certain combinations of `s' and `sym'
   combinations.  *)
  VAR
    pos: LONGINT;
  BEGIN
    IF (sym = s) THEN
      GetSym
    ELSE
      (* have error point just after the end of the last symbol or at the 
         beginning of the current one *)
      IF (s = semicolon) OR (s = colon) OR (s = comma) OR (s = period) OR
         (s = lParen) OR (s = lBrak) OR (s = lBrace) OR
         (s = rParen) OR (s = rBrak) OR (s = rBrace) THEN
        pos := lastSymEnd
      ELSE
        pos := currSymPos
      END;
      (* just numerate the error messages according to the token codes *)
      E.Err (pos, 100+LONG (s));
      IF (s = becomes) & ((sym = eql) OR (sym = colon)) OR
         (s = eql) & (sym = becomes) OR 
         ((of <= s) & (s <= by) OR
          (end <= s) & (s <= module)) & (sym = ident) THEN
        GetSym
      END
    END
  END CheckSym;

PROCEDURE PopCond;
  BEGIN
    condStack := condStack. prev         (* remove top of stack *)
  END PopCond;

PROCEDURE ParsePragma;
(* Parses commands enclosed in <* .. *>.  See `frontend/doc/Pragmas' for 
   details.  *)

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
      string: Data.String;
      pos: LONGINT;
    END;
    
  VAR
    evalText, dummy, err, nested: BOOLEAN;
    ins: ARRAY 16 OF CHAR;
    currentUnderscore: BOOLEAN;
    
  PROCEDURE CheckName (VAR name: ARRAY OF CHAR);
    BEGIN
      IF (name = "TRUE") OR (name = "FALSE") OR (name = "PUSH") OR 
         (name = "POP") OR (name = "DEFINE") THEN
        E.Err (currSymPos, 21)           (* illegal variable name *)
      END
    END CheckName;
  
  PROCEDURE CheckBoolean (eval: BOOLEAN; VAR value: Value);
    BEGIN
      IF (value. type # tpBoolean) & (value. type # tpUndef) THEN
        IF eval THEN
          E.Err (value. pos, 20)         (* boolean expression expected *)
        END;
        value. type := tpBoolean;
        value. boolean := FALSE
      END
    END CheckBoolean;
  
  PROCEDURE Expression (eval: BOOLEAN; VAR value: Value);
    VAR
      right: Value;
      pos: LONGINT;
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
            value. pos := currSymPos;
            IF (sym = ident) THEN
              IF (str^ = "FALSE") OR (str^ = "TRUE") THEN (* boolean const *)
                value. type := tpBoolean;
                value. boolean := (str^ = "TRUE")
              ELSE                       (* variable *)
                CheckName (str^);
                pragma := ParamPragmas.pragmas. Find (str^);
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
                  E.Err (currSymPos, 17) (* undeclared pragma variable *)
                END
              END;
              GetSym
            ELSIF (sym = number) & (numType = numInt) THEN (* int const *)
              value. type := tpInteger;
              value. integer := intVal;
              GetSym
            ELSIF (sym = string) THEN    (* string const *)
              value. type := tpString;
              NEW (value. string, Strings.Length (str^)+1);
              COPY (str^, value. string^);
              GetSym
            ELSIF (sym = lParen) THEN    (* parenthesis *)
              GetSym;
              Expression (eval, value);
              CheckSym (rParen)
            ELSIF (sym = not) THEN       (* negation *)
              GetSym;
              Expression (eval, value);
              CheckBoolean (eval, value);
              value. boolean := ~value. boolean
            ELSE
              E.Err (currSymPos, 181);   (* factor starts with illegal sym *)
              GetSym
            END
          END Factor;
        
        BEGIN
          Factor (eval, value);
          WHILE (sym = and) DO
            CheckBoolean (eval, value);
            value. pos := currSymPos;
            GetSym;
            Factor (eval & value. boolean, right);
            CheckBoolean (eval & value. boolean, right);
            value. boolean := value. boolean & right. boolean
          END
        END Term;
      
      BEGIN
        Term (eval, value);
        WHILE (sym = or) DO
          CheckBoolean (eval, value);
          value. pos := currSymPos;
          GetSym;
          Term (eval & ~value. boolean, right);
          CheckBoolean (eval & ~value. boolean, right);
          value. boolean := value. boolean OR right. boolean
        END
      END SimpleExpr;
    
    BEGIN
      SimpleExpr (eval, value);
      IF (eql <= sym) & (sym <= geq) THEN
        op := sym; pos := currSymPos;
        GetSym;
        SimpleExpr (eval, right);
        IF ~eval OR (value. type = tpUndef) OR (right. type = tpUndef) THEN
          (* ignore *)
        ELSIF (value. type # right. type) THEN
           E.ErrIns (pos, 233, "")       (* operand incompatible to lhs *)
        ELSIF (value. type = tpBoolean) & (lss <= sym) & (sym <= geq) THEN
           E.ErrIns (pos, 231, "boolean") (* operator not applicable to bool *)
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
        value. pos := pos;
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
      cond. ifPos := currSymPos;
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
        E.Err (currSymPos, 14);          (* no open IF statement *)
        PushCond
      ELSIF noElse & condStack. elsePresent THEN
        E.Err (currSymPos, 15);          (* ELSE part already declared *)
        PushCond
      END
    END CheckForIf;
  
  PROCEDURE Assignment (define, eval: BOOLEAN);
  (* define=TRUE: defining assignment, eval=TRUE: execute assignment *)
    VAR
      name: Param.LargeString;
      pragma: ParamPragmas.Pragma;
      value: Value;
      pos: LONGINT;
    BEGIN
      IF (sym = ident) THEN
        IF eval THEN
          pragma := ParamPragmas.pragmas. Find (str^);
          pos := currSymPos;
          CheckName (str^);
          COPY (str^, name);
          IF (pragma = NIL) & ~define THEN
            E.Err (currSymPos, 17)       (* undeclared pragma variable *)
          ELSIF (pragma # NIL) & define THEN
            E.Err (currSymPos, 18)       (* pragma variable already defined *)
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
                E.ErrIns (value. pos, 19, ins) (* not assignment compatible *)
              ELSE
                StdTypes.NotifyPragmaAssign (pragma, pos)
              END
            END
          END
        ELSE  (* don't execute, just do syntax check *)
          GetSym;
          CheckSym (becomes);
          Expression (eval, value)
        END
      ELSE
        E.Err (currSymPos, 100)
      END
    END Assignment;
  
  BEGIN  (* pre: sym = "<*" *) 
    currentUnderscore := allowUnderscore;
    allowUnderscore := TRUE;
    evalText := TRUE;
    REPEAT
      GetSym;
      scanStatus := inPragma;
      LOOP
        nested := (sym = if) OR (sym = elsif) OR (sym = else);
        IF (sym = if) OR (sym = elsif) THEN
          IF (sym = if) THEN
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
        ELSIF (sym = else) THEN
          CheckForIf (TRUE);
          condStack. elsePresent := TRUE;
          GetSym;
          evalText := ~condStack. skippedCond & ~condStack.foundTrue;
        ELSIF (sym = end) THEN
          CheckForIf (FALSE);
          evalText := ~condStack. skippedCond;
          PopCond;  (* remove top of stack *)
          GetSym
        ELSIF (sym = ident) & (str^ = "DEFINE") THEN
          GetSym;
          Assignment (TRUE, evalText)
        ELSIF (sym = ident) & (str^ = "PUSH") THEN
          IF evalText THEN ParamPragmas.Push END;
          GetSym
        ELSIF (sym = ident) & (str^ = "POP") THEN
          IF evalText THEN
            IF (ParamPragmas.pragmas. stackLevel = 0) THEN
              E.Err (currSymPos, 16)       (* pragma stack empty *)
            ELSE
              ParamPragmas.Pop
            END
          END;
          GetSym
        ELSIF (sym = ident) THEN
          Assignment (FALSE, evalText)
        END;
        IF (sym = semicolon) THEN
          GetSym
        ELSIF (sym # end) & ((sym = pragmaEnd) OR ~nested) THEN
          EXIT
        END
      END;
      scanStatus := skippingText;
      CheckSym (pragmaEnd);
      IF ~evalText THEN
        (* skip Oberon-2 text inside conditional statement *)
        WHILE (sym # pragmaStart) & (sym # endOfFile) DO
          GetSym
        END
      END
    UNTIL (sym # pragmaStart);
    allowUnderscore := currentUnderscore;
    scanStatus := normal
  END ParsePragma;

PROCEDURE CheckPragmas*;
  BEGIN
    WHILE (condStack # NIL) DO
      E.Err (condStack. ifPos, 13);  (* condition lacks END *)
      PopCond
    END
  END CheckPragmas;

PROCEDURE Close*;
  BEGIN
    IF (inFile # NIL) THEN
      inFile. Close;
      inFile := NIL;
      finished := TRUE;
      
      IF ~incrementalRead THEN
        INC (sourceTotal, pos);
        INC (sourceLines, eolCounter+1)
      END
    END
  END Close;

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
      Strings.Append (E.sourceFile^, msg);
      Param.FatalError (msg)
    END
  END ReadBlock;



PROCEDURE Comment;
(* Skips comment (may include nested comments).
   pre: scan[pos]="*", scan[pos-1]="("
   post: `pos' is the index of the first character behind the comment, or 
     `buf[pos]=eof'.
   side: An unterminated comment will cause an error message. *)
  VAR
    start: LONGINT;
  BEGIN
    start := pos-1;
    INC (pos);
    LOOP  (* loop until end of comment/file reached *)
      IF incrementalRead & (currLen # fileLen) & (currLen-pos < sizeBlock DIV 2) THEN
        ReadBlock
      END;
      CASE buf[pos] OF
      | eof:                             (* end of file? *)
        IF (pos = fileLen) THEN
          E.Err (start, 1);              (* comment not terminated *)
          EXIT
        ELSE
          INC (pos)
        END
      | eol:
        EndOfLine;
        INC (pos)
      | "*":
        INC (pos);
        IF (buf[pos] = ")") THEN         (* end of comment *)
          INC (pos);
          EXIT
        END
      | "(":
        INC (pos);
        IF (buf[pos] = "*") THEN         (* nested comments *)
          Comment
        END
      ELSE                               (* skip characters in comment *)
        INC (pos)
      END
    END
  END Comment;

PROCEDURE StoreString (from, to: LONGINT); 
(* Store the characters `buf[from..to-1]' in `str^'.  If `str^' is too small
   increase its size (in steps of `incrString').  *)
  CONST
    incrString = 128;
  VAR
    i: LONGINT;
  BEGIN
    (* allocate new string buffer if the current one is too small *)
    IF (to-from >= LEN(str^)) THEN
      i := LEN(str^);
      WHILE (i <= to-from) DO
        INC (i, incrString)
      END;
      NEW (str, i)
    END;
    (* copy characters from file buffer into string buffer *)
    i := 0;
    WHILE (from # to) DO
      str[i] := buf[from]; INC (from); INC (i)
    END;
    str[i] := 0X
  END StoreString;

PROCEDURE GetString (end: CHAR);
(* Read string with double or single quote as delimiter.
   pre: buf[pos]=end
   post: `buf[pos-1]=end' (i.e. `pos' is placed behind the string's ending 
     delimiter or `buf[pos]=eof'. `sym' is  set to `string', a copy of the 
     string is placed in `str'.
   side: Control characters in the string or a not terminated string will be
     marked with error messages. *)
  VAR
    start: LONGINT;
    ins: ARRAY 16 OF CHAR;
  BEGIN
    sym := string;
    start := pos;
    LOOP  (* loop until end or eof reached *)
      INC (pos);
      IF (buf[pos] < " ") THEN           (* illegal control character or eof *)
        IF (buf[pos] = eof) & (pos = fileLen) OR (buf[pos] = eol) THEN
          E.Err (start, 3); 
          IF (buf[pos] = eol) THEN
            INC (pos);
            EndOfLine
          END;
          EXIT         (* string not terminated *)
        ELSE
          E.Err (pos, 2)                 (* string contains illegal char *)
        END
      ELSIF (buf[pos] = end) THEN        (* end of string *)
        INC (pos); EXIT
      END
    END;
    StoreString (start+1, pos-1);
    intVal := ORD (str[0]);              (* used for character constants *)
    IF (stringLength. value # MIN (LONGINT)) &
       (pos-start-2 > ABS (stringLength. value)) THEN
      IntStr.IntToStr (ABS (stringLength. value), ins);
      IF (stringLength. value < 0) THEN
        E.ErrIns (-start, 31, ins)    (* warning: string longer than x chars *)
      ELSE
        E.ErrIns (start, 30, ins)     (* string too long *)
      END
    END
  END GetString;

PROCEDURE Ident;
(* Reads identifiers and keywords.
   pre: `buf[pos]' is a character
   post: `buf[pos]' isn't a character or a cypher, `sym' is set to ident or
     to the corresponding keyword, a copy of the identifier is stored in 
     `str'. *)
  VAR
    start, sum, i: LONGINT;
    ins: ARRAY 16 OF CHAR;
    
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
    sym := ident; sum := 0; start := pos;
    IF moduleIdent THEN
      SkipWord;
      WHILE (buf[pos] = moduleSeparator) & (buf[pos+1] # "=") DO
        INC (pos);
        IF IsChar (FALSE) THEN
          SkipWord
        ELSE
          E.Err (start, 35)    (* malformed module identifier *)
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
    StoreString (start, pos);
    
    IF ~allowUnderscore THEN
      i := start;
      WHILE (i # pos) DO
        IF (buf[pos] = "_") THEN
          E.Err (i, 10)                  (* illegal character *)
        END;
        INC (i)
      END
    END;
    
    (* compare identifier against list of keywords; 
       modify `sym' if it matches one of them *)
    i := sum MOD sizeKWTable;
    IF (kwSym[i, 0] >= 0) THEN
      IF CompareIdent (kwStr[i, 0]) THEN
        sym := kwSym[i, 0]
      ELSIF (kwSym[i, 1] >= 0) & CompareIdent (kwStr[i, 1]) THEN
        sym := kwSym[i, 1]
      END
    END;
    IF (sym = ident) & (identLength. value # MIN (LONGINT)) &
       (pos-start > ABS (identLength. value)) THEN
      IntStr.IntToStr (ABS (identLength. value), ins);
      IF (identLength. value < 0) THEN
        E.ErrIns (-start, 33, ins)    (* warning: ident longer than x chars *)
      ELSE
        E.ErrIns (start, 32, ins)     (* ident too long *)
      END
    END
  END Ident;

PROCEDURE Number;
(* Parses and converts numbers (this includes character, decimal, real, and 
   long real constants).
   pre: `buf[pos]' is a cypher
   post: The number's internal representation is computed. If it is a real, its
     value is stored in `realVal' (numType=numReal or numLReal, sym=number),
     otherwise its integer value is placed in `intVal' (numType=intVal, 
     sym=number). If it was a character constant (suffix X) it's converted into
     a string (in `str', sym=string). *)
  VAR
    real: REAL;
    format: SHORTINT;
    start, i: LONGINT;

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
        E.Err (spos, 6)                 (* number out of range *)
      ELSIF (spos <= epos) THEN         (* if any non-zero cyphers follow *)
        result := GetCypher (buf[spos]);
        INC (spos);
        IF (epos-spos = 6) & (result >= 8) THEN
          (* value is beyond MAX(LONGINT)=07FFFFFFFH: correct this by sub-
             tracting 16 from the value of the most significant digit, creating
             the negative number that matches the bit pattern *)
          E.Err (start, -34); (* warning: hex const mapped to negative value *)
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
    sym := number; start := pos;
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
        numType := numLReal; buf[pos] := "E"
      ELSE
        numType := numReal
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
          E.Err (pos, 9)                 (* illegal exponent format *)
        END
      END;
      StoreString (start, pos);
      (* convert constant *)
      IF (numType = numReal) THEN
        RealStr.StrToReal (str^, real, format);
        realVal := real
      ELSE
        LRealStr.StrToReal (str^, realVal, format)
      END;
      IF (format = LRealStr.strOutOfRange) OR
         (numType = numReal) & ~StdTypes.ValidReal (realVal) THEN
        E.Err (start, 6)                 (* number out of range *)
      END
    ELSE  (* integer *)
      intVal := 0;
      (* determine base of representation *)
      IF (buf[pos] = "H") OR (buf[pos] = "X") THEN
        intVal := ConvertHex (start, pos-1);
      ELSE
        (* check whether all characters are decimal digits *)
        i := start;
        WHILE (i # pos) & ("0" <= buf[i]) & (buf[i] <= "9") DO
          INC (i)
        END;
        IF (i # pos) THEN                (* buf[i] isn't from "0".."9" *)
          intVal := 1; E.Err (i, 5)      (* illegal cypher *)
        ELSE
          StoreString (start, pos);
          IntStr.StrToInt (str^, intVal, format);
          IF (format = IntStr.strOutOfRange) THEN
            intVal := 1; E.Err (start, 6)  (* number out of range *)
          END
        END
      END;
      (* set constant type according to suffix *)
      IF (buf[pos] = "X") THEN
        sym := string; INC (pos);
        IF StdTypes.ValidChar (intVal) THEN
          str[0] := "a"; str[1] := 0X    (* parser takes value from `intVal' *)
        ELSE
          E.Err (start, 7)               (* not a legal character constant *)
        END
      ELSE
        IF (buf[pos] = "H") THEN INC (pos) END;
        numType := numInt
      END
    END
  END Number;

PROCEDURE GetSym*;
(* Reads next token.
   pre: `Init' has been executed without any errors.
   post: `sym' denotes the class of the token, its attributes are stored in
     `str', `numType', `intVal' and `realVal' (depending on the class). *)
  VAR
    p0: LONGINT;
  BEGIN
    IF incrementalRead & (currLen#fileLen) & (currLen-pos < sizeBlock DIV 2) THEN
      ReadBlock
    END;
    
    lastSymEnd := pos;
    (* skip whitespace characters *)
    WHILE (buf[pos] <= " ") DO
      IF (buf[pos] = eof) & (pos = fileLen) THEN
        sym := endOfFile;
        RETURN
      ELSIF (buf[pos] = eol) THEN
        EndOfLine;
        INC (pos)
      ELSE
        INC (pos)
      END
    END;
    
    currSymPos := pos;
    CASE buf[pos] OF
    | "a".."z", "A".."Z", "_": Ident
    | "0".."9": Number
    | '"', "'": GetString (buf[pos])
    | "~": sym := not; INC (pos)
    | "{": sym := lBrace; INC (pos)
    | ".": 
      INC (pos);
      IF (buf[pos] = ".") THEN 
        sym := upto; 
        INC (pos)
      ELSE 
        sym := period
      END
    | "^": sym := arrow; INC (pos)
    | "[": sym := lBrak; INC (pos)
    | ":": 
      INC (pos);
      IF (buf[pos] = "=") THEN 
        sym := becomes; INC (pos)
      ELSE 
        sym := colon
      END
    | "(": 
      INC (pos);
      IF (buf[pos] = "*") THEN 
        p0 := lastSymEnd; Comment; GetSym; lastSymEnd := p0
      ELSE 
        sym := lParen
      END
    | "*": 
      sym := times; INC (pos);
      IF (buf[pos] = ")") THEN
        E.Err (currSymPos, 4);           (* no comment started *)
        INC (pos)
      ELSIF (buf[pos] = ">") THEN
        IF (scanStatus = inPragma) THEN
          sym := pragmaEnd; INC (pos)
        ELSE
          E.Err (pos-1, 11);             (* no <* opened *)
          INC (pos)
        END
      END
    | "/": sym := slash; INC (pos)
    | "&": sym := and; INC (pos)
    | "+": sym := plus; INC (pos)
    | "-": sym := minus; INC (pos)
    | "=": sym := eql; INC (pos)
    | "#": sym := neq; INC (pos)
    | "<": 
      INC (pos);
      IF (buf[pos] = "=") THEN 
        sym := leq; INC (pos)
      ELSIF (buf[pos] = "*") THEN
        IF (scanStatus = inPragma) THEN
          E.Err (pos-1, 12);             (* nested <* *)
          GetSym
        ELSIF (scanStatus = skippingText) THEN
          sym := pragmaStart; INC (pos)
        ELSE  (* (scanStatus = normal) *)
          INC (pos);
          ParsePragma
        END
      ELSE 
        sym := lss 
      END
    | ">": 
      INC (pos);
      IF (buf[pos] = "=") THEN 
        sym := geq; INC (pos)
      ELSE 
        sym := gtr
      END
    | "}": sym := rBrace; INC (pos)
    | ")": sym := rParen; INC (pos)
    | "]": sym := rBrak; INC (pos)
    | "|": sym := bar; INC (pos)
    | ";": sym := semicolon; INC (pos)
    | ",": sym := comma; INC (pos)
    ELSE
      E.Err (currSymPos, 8);             (* illegal symbol *)
      INC (pos); GetSym
    END
  END GetSym;

PROCEDURE SaveScanPos* (VAR state: ScanState);
(* Stores the current state of the scanner, most of all the current reading
   position, into `state'.  *)
   
  PROCEDURE Copy (cond: ConditionStack): ConditionStack;
    VAR
      new: ConditionStack;
    BEGIN
      IF (cond = NIL) THEN
        RETURN NIL
      ELSE
        NEW (new);
        new^ := cond^;
        new. prev := Copy (cond. prev);
        RETURN new
      END
    END Copy;
    
  BEGIN
    state. pos := currSymPos;
    (* store duplicate of condition stack *)
    state. condStack := Copy (condStack);
    (* store state of variables *)
    ParamPragmas.Save (state. pragmaState)
  END SaveScanPos;

PROCEDURE RestoreScanPos* (VAR state: ScanState);
(* Restores state of scanner from `state'.  *)
  BEGIN
    pos := state. pos;
    condStack := state. condStack;
    ParamPragmas.Restore (state. pragmaState);
    GetSym
  END RestoreScanPos;

PROCEDURE SetSym* (newSym: SHORTINT);
(* Sets value of `sym' to `newSym'.  *)
  BEGIN
    sym := newSym
  END SetSym;


PROCEDURE ThreeDots* (read: BOOLEAN): BOOLEAN;
(* Result is TRUE if the current token can be interpreted as `...' (this isn't
   a legal symbol).  In this case the input position is set right after the
   final `.' if `read=TRUE', otherwise the token stream isn't changed.  *)
  BEGIN
    IF (sym = upto) & (buf[pos] = ".") THEN
      IF read THEN
        INC (pos)
      END;
      RETURN TRUE
    ELSE
      RETURN FALSE
    END
  END ThreeDots;



PROCEDURE Name2File* (VAR name: ARRAY OF CHAR);
  VAR
    i: LONGINT;
  BEGIN
    i := 0;
    WHILE (name[i] # 0X) DO
      IF (name[i] = moduleSeparator) THEN
        name[i] := "/";
      END;
      INC (i)
    END
  END Name2File;

PROCEDURE Init* (fileName: ARRAY OF CHAR; incrRead: BOOLEAN);
(* Reads contents of file `fileName' into the internal buffer.  If `fileName'
   matches an RCS file name, the file is checked out first, and the contents
   of the working file are read.  The name of the file is stored in 
   `E.sourceFile' (it differs from `fileName' in the case of RCS files).  On
   success the first token is read by calling `GetSym'.  A failure to open or 
   to read the file will abort the program by calling `Param.FatalError'.  
   `incrRead=TRUE' enables incremental reading.  This means that, instead of 
   reading the whole file at once, only chunks of `sizeBlock' bytes are read on
   demand.  This should only be used for the Make utility, since it limits
   the maximum length of strings and identifiers to `sizeBlock DIV 2', and an
   overflow is not detected.  *)
  CONST
    firstBuffer = 32*1024-16;            
    (* initial size of file buffer; make sure that buffer+tag fit closely into
       a block of 2^n bytes *)
    incrBuffer = 16*1024;
    (* step by which the buffer size is incremented if the current buffer isn't
       large enough to hold the next file; should be some 2^n *)
  VAR
    i: LONGINT;
    res: Files.Result;
    msg: ARRAY 1024 OF CHAR;
  BEGIN
    incrementalRead := incrRead;
    finished := TRUE;
    IF ParamPaths.paths. rcsEnabled & VC.MasterFile (fileName) THEN
      IF VC.CheckOut (fileName, msg) THEN
        E.VerboseMsg (msg)  (* success, write checkout command if --verbose *)
      ELSE  (* failure, abort with error message *)
        Param.FatalError (msg)
      END
    END;
    
    inFile := Files.Old (fileName, {Files.read}, res);
    NEW (E.sourceFile, Strings.Length (fileName)+1);
    COPY (fileName, E.sourceFile^);      (* store file name actually used *)
    IF (inFile = NIL) THEN
      msg := "File ";
      Strings.Append (fileName, msg);
      Strings.Append (" not found", msg);
      Param.FatalError (msg)
    ELSE
      fileLen := inFile. Length();
      (* allocate buffer *)
      IF (buf = NIL) OR (LEN(buf^) < fileLen+1) THEN
        IF (buf = NIL) THEN
          i := firstBuffer
        ELSE
          i := LEN(buf^)
        END;
        WHILE (i <= fileLen+1) DO       (* increase buffer size if necessary *)
          INC (i, incrBuffer)
        END;
        NEW (buf, i)
      END;
      
      buf[fileLen] := eof; currLen := 0; pos := 0; eolCounter := 0;
      condStack := NIL; scanStatus := normal; finished := FALSE;
      allowUnderscore := FALSE; moduleIdent := FALSE;
      
      (* read file *)
      inReader := inFile. NewReader();
      ReadBlock;
      GetSym                           (* initialize token stream *)
    END
  END Init;

PROCEDURE CatchSignal;
  BEGIN
    IF ~finished THEN
      E.Err (pos, 999);                  (* unexpected compiler termination *)
      E.EmitErrors (TRUE)
    END
  END CatchSignal;


PROCEDURE InitKeywords;
(* Fills hash table used by `Ident' to identify the keywords. *)
  VAR
    i: INTEGER;

  PROCEDURE KW (ident: ARRAY OF CHAR; sym: SHORTINT);
    VAR
      i, sum: INTEGER;
    BEGIN
      sum := 0; i := 0;
      WHILE (ident[i] # 0X) DO
        INC (sum, ORD (ident[i])); INC (i)
      END;
      i := sum MOD sizeKWTable;
      IF (kwSym[i, 0] < 0) THEN
        kwSym[i, 0] := sym;
        COPY (ident, kwStr[i, 0])
      ELSE
        kwSym[i, 1] := sym;
        COPY (ident, kwStr[i, 1])
      END
    END KW;

  BEGIN
    FOR i := 0 TO sizeKWTable-1 DO
      kwSym[i, 0] := -1; kwSym[i, 1] := -1;
      kwStr[i, 0, 0] := 0X; kwStr[i, 1, 0] := 0X
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
  buf := NIL;
  inFile := NIL;
  NEW (str, 128-16);  (* let str+tag fit closely into a 2^n bytes block *)
  NEW (eolArray, 1024-4);
  InitKeywords;
  finished := TRUE;
  sourceTotal := 0; sourceLines := 0;
  
  stringLength := ParamOptions.CreateInteger ("StringLength", 
                     Config.defaultStringLength, MIN (LONGINT), MAX (LONGINT));
  ParamPragmas.pragmas. Add (stringLength);
  identLength := ParamOptions.CreateInteger ("IdentLength", 
                      Config.defaultIdentLength, MIN (LONGINT), MAX (LONGINT));
  ParamPragmas.pragmas. Add (identLength);
  allowUnderscore := FALSE;
  moduleIdent := FALSE;
  
  Termination.RegisterProc (CatchSignal)
END Scanner.

