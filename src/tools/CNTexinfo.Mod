(* 	$Id: CNTexinfo.Mod,v 1.10 2000/08/20 13:38:55 ooc-devel Exp $	 *)
MODULE CNTexinfo;
(*  A parser of embedded Texinfo comments.
    Copyright (C) 1999, 2000  Michael van Acken

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
  Ascii, CharClass, Strings, Out, S := CNScanner, Decoration := CNDecoration;
  

(*
This is the list of recognized Texinfo commands.  To add a new command
to the module, you must do the following:

  1. Add a new constant to the list below.  Make sure that you add 
     it to the right class.  The value or the order assigned to the
     commands is of no importance.
  
  2. Add a new call to Register() in the module body for the new 
     command.
  
  3. If necessary, add any additional semantic checks to this module
     for the command in question.
  
  4. Extend the conversion modules (CNTexi2Text, CNTexi2HTML, CNTexi2Texi)
     to deal with the new command.

The following commands are on the "to do" list and should be included in
to "final" version: @enumerate, @format, @quotation.
*)

CONST
  (* Class 1: Non-alphabetic commands.  These commands never take any 
              argument.  They are never followed by braces.  *)
  class1Low* = 0;
  cmdAtGlyph* = class1Low+0;
  cmdLeftBrace* = class1Low+1;
  cmdRightBrace* = class1Low+2;
  class1High* = cmdRightBrace;
  
  (* Class 2: Alphabetic commands that do not require arguments.  These 
              commands start with @ followed by a word followed by left-
              and right-hand braces.  *)
  class2Low* = class1High+1;
  cmdBullet* = class2Low+0;
  cmdDots* = class2Low+1;
  cmdMinus* = class2Low+2;
  cmdResult* = class2Low+3;
  class2High* = cmdResult;
  
  (* Class 3: Alphabetic commands that require arguments within braces.
             These commands start with @ followed by a letter or a word,
             followed by an argument within braces.  *)
  class3Low* = class2High+1;
  cmdArg* = class3Low+0;                 (* pseudo command *)
  cmdAsis* = class3Low+1;
  cmdCite* = class3Low+2;
  cmdCode* = class3Low+3;
  cmdDfn* = class3Low+4;
  cmdEmail* = class3Low+5;
  cmdEmph* = class3Low+6;
  cmdFile* = class3Low+7;
  cmdKbd* = class3Low+8;
  cmdOberonModule* = class3Low+9;
  cmdOberonConst* = class3Low+10;
  cmdOberonField* = class3Low+11;
  cmdOberonParam* = class3Low+12;
  cmdOberonProc* = class3Low+13;
  cmdOberonType* = class3Low+14;
  cmdOberonVar* = class3Low+15;
  cmdSamp* = class3Low+16;
  cmdStrong* = class3Low+17;
  cmdUref* = class3Low+18;
  cmdUrl* = class3Low+19;
  cmdVar* = class3Low+20;
  class3High* = cmdVar;
  
  (* Class 4: Alphabetic commands that occupy an entire line.
              These commands occupy an entire line.  The line starts with @,
              followed by the name of the command (a word).  If no argument
              is needed, the word is followed by the end of the line.  If 
              there is an argument, it is separated from the command name by
              a space.  Braces are not used.  *)
  class4Low* = class3High+1;
  cmdEnd* = class4Low+0;
  cmdExample*= class4Low+1;
  cmdItem* = class4Low+2;
  cmdItemize* = class4Low+3;
(*  cmdItemX* = class4Low+X;*)
  cmdNoIndent* = class4Low+4;
  cmdPreCond* = class4Low+5;
  cmdPostCond* = class4Low+6;
  cmdTable* = class4Low+7;
  class4High* = cmdTable;
  
  (* miscellaneous commands that do not start with @, but nevertheless
     have an effect on the output *)
  cmdParagraphSep* = class4High+1;
  cmdEmDash* = class4High+2;
  cmdTextFragment* = class4High+3;
  cmdEndOfBrace* = class4High+4;
  cmdEndOfLine* = class4High+5;
  cmdEndOfText* = class4High+6;


TYPE  (* text is represented as a sequence of elements *)
  TextElement* = POINTER TO TextElementDesc;
  TextElementDesc* = RECORD  (* abstract class *)
    prevElement-, nextElement-: TextElement;
  END;

TYPE
  Token* = POINTER TO TokenDesc;
  TokenDesc = RECORD
    (TextElementDesc)
    line-, column-: LONGINT; (* symbol position (analogous to S.Symbol);
                                relative to start of document *)
    pos-: LONGINT;           (* dito, counted in characters starting with 0 *)
    cmdId-: LONGINT;         (* command identifier *)
    string-: S.String;       (* string value (for text fragments) *)
  END;

(* ------------------------------------------------------------------------ *)

TYPE
  MarkedText* = POINTER TO MarkedTextDesc;
  MarkedTextDesc = RECORD
    (TextElementDesc)
    cmdId-: LONGINT;
    content-: TextElement;
    (* a list of text element that are part of the "{..}" sequence; the list
       is composed of instances of Token (i.e., text fragments) and other
       instances of `MarkedText'  *)
  END;

TYPE
  Block* = POINTER TO BlockDesc;
  BlockDesc = RECORD
    (TextElementDesc)
    start-: Token;
    (* The token that starts the block.  If the block stands for a paragraph,
       this field is NIL.  An start command of name "foo" designates a block
       "@@foo .. @@end foo".  *)
    lineArgs-: TextElement;
    (* If the block begins with a line command, this is the list of arguments
       following the command on the same line.  NIL means an empty line
       command.  *)
    content-: TextElement;
    (* list of text element that are part of this block *)
    padBefore-, padAfter-: BOOLEAN;
    (* if TRUE, then insert an empty line before and/or after the block in the
       ASCII output; has no effect for the HTML or TeX version *)
  END;

(* ------------------------------------------------------------------------ *)

TYPE
  Texinfo* = POINTER TO TexinfoDesc;
  TexinfoDesc = RECORD
    (S.InfoDesc)
    text-: S.TextSymbol;
    decoration-: Decoration.Decoration;
    textElements: TextElement;
    content-: TextElement;
  END;
  

VAR
  class1: ARRAY 256 OF SHORTINT;
  cmdList: ARRAY class4High+1 OF RECORD
    class: SHORTINT;
    name: ARRAY 16 OF CHAR;
    argLow, argHigh: SHORTINT;
  END;
  emptyString: S.String;
  

PROCEDURE InitTextElement (elem: TextElement);
  BEGIN
    elem. prevElement := NIL;
    elem. nextElement := NIL
  END InitTextElement;

PROCEDURE InitToken (token: Token; cmdId, pos, line, column: LONGINT);
  BEGIN
    InitTextElement (token);
    token. pos := pos;
    token. line := line;
    token. column := column;
    token. cmdId := cmdId;
    token. string := NIL
  END InitToken;

PROCEDURE InitBlock (block: Block);
  BEGIN
    InitTextElement (block);
    block. start := NIL;
    block. lineArgs := NIL;
    block. content := NIL;
    block. padBefore := FALSE;
    block. padAfter := FALSE
  END InitBlock;


PROCEDURE GetString (VAR str: ARRAY OF CHAR; start, end: LONGINT): S.String;
  VAR
    s: S.String;
    i, j: LONGINT;
  BEGIN
    NEW (s, end-start+1);
    i := start; j := 0;
    WHILE (i # end) DO
      s[j] := str[i];
      INC (i); INC (j)
    END;
    s[j] := 0X;
    RETURN s
  END GetString;

PROCEDURE NewFragment (string: S.String; pos, line, column: LONGINT): Token;
  VAR
    t: Token;
  BEGIN
    NEW (t);
    InitToken (t, cmdTextFragment, pos, line, column);
    t. string := string;
    RETURN t
  END NewFragment;

PROCEDURE NewCommand (cmd: LONGINT; pos, line, column: LONGINT): Token;
  VAR
    t: Token;
  BEGIN
    NEW (t);
    InitToken (t, cmd, pos, line, column);
    RETURN t
  END NewCommand;


PROCEDURE Tokenize (sym: S.TextSymbol): Texinfo;
(* Tokenizes the Texinfo string in the comment `sym' and returns a Texinfo
   object with the token list and the decoration information.  Result is NIL
   if an error was found.
   
   NOTE: This procedure must be called with position information in `sym'
   intact, i.e., before `Scanner.Abs2Rel' is called.  *)
  VAR
    noerr: BOOLEAN;
    pos, i, currLine, currLinePos, currLineTab, currColumn, len: LONGINT;
    inLineCommand, tableCommand: BOOLEAN;
    textPos, textLine, textColumn: LONGINT;
    str: S.String;
    seqHead, seqTail: TextElement;
    name: ARRAY 16 OF CHAR;
    texinfo: Texinfo;
    decoration: Decoration.Decoration;
    
  PROCEDURE Error (pos: LONGINT; msg0, msg1, msg2: ARRAY OF CHAR);
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
      Out.LongInt (sym.pos+pos, 0);
      Out.String (": ");
      Out.String (msg0);
      Out.String (msg1);
      Out.String (msg2);
      Out.Ln;
      noerr := FALSE
    END Error;

  PROCEDURE Append (te: TextElement);
    BEGIN
      te. prevElement := seqTail;
      te. nextElement := NIL;
      IF (seqHead = NIL) THEN
        seqHead := te; seqTail := te
      ELSE
        seqTail. nextElement := te
      END;
      seqTail := te
    END Append;

  PROCEDURE LookingAtEOL (str: S.String; pos: LONGINT): BOOLEAN;
    BEGIN
      RETURN (pos = -1) OR (str[pos] = 0X) OR
             (str[pos] = Ascii.cr) OR (str[pos] = Ascii.lf)
    END LookingAtEOL;

  PROCEDURE BeginningOfLine (str: S.String; pos: LONGINT): BOOLEAN;
    BEGIN
      REPEAT
        DEC (pos);
        IF (pos >= 0) & (str[pos] > " ") THEN
          RETURN FALSE
        END
      UNTIL LookingAtEOL (str, pos);
      RETURN TRUE
    END BeginningOfLine;
  
  PROCEDURE AppendText (origStr: S.String; from, to: LONGINT);
    VAR
      str: S.String;
      endOfText: BOOLEAN;
      pos, delta, lastNonWS, start: LONGINT;
    BEGIN
      IF (from # to) THEN        (* got non-empty text fragment *)
        endOfText := (origStr[to] = 0X);
        str := GetString (origStr^, from, to);
(*Out.String ("<ORIGINAL_STRING>");
Out.String (str^);
Out.String ("</ORIGINAL_STRING>"); Out.Ln;*)

        pos := 0;
        IF LookingAtEOL (origStr, from-1) THEN
(*OBSOLETE          (* `from' is pointing to the beginning of a line; strip any leading
             whitespace from the string, and update the variables `textPos',
             `textLine', and `textColumn' to point to the first non-whitespace
             character in the string; if the string has only whitespace
             characters, make them point to the end of the string *)
          WHILE (0X < str[pos]) & (str[pos] <= " ") DO
            IF (str[pos] = Ascii.ht) THEN
              INC (textColumn, S.tabWidth-textColumn MOD S.tabWidth)
            ELSIF (str[pos] = Ascii.lf) THEN
              INC (textLine);
              textColumn := 0
            ELSIF (str[pos] = Ascii.cr) THEN
              INC (textLine);
              textColumn := 0;
              IF (str[pos+1] = Ascii.lf) THEN
                INC (textPos); INC (pos)
              END
            END;
            INC (textPos); INC (pos)
          END;*)
          delta := pos
        ELSE
          delta := 0
        END;
        
        (* here we are looking at the first non-whitespace in the string, or at
           the end of the string *)
        WHILE (str[pos] # 0X) DO
          (* str[pos] is not whitespace; copy data upto end of line *)
          lastNonWS := pos-1;
          WHILE ~LookingAtEOL (str, pos) DO
            str[pos-delta] := str[pos];
(*OBSOLETE            IF (str[pos] > " ") THEN*)
              lastNonWS := pos;
(*OBSOLETE            END;*)
            INC (pos)
          END;
          IF (lastNonWS >= 0) & (str[lastNonWS] = "@") THEN
            (* make sure that nobody clobbers things like "@ "=="@SPACE" *)
            INC (lastNonWS)
          END;
          (* remove trailing whitespace from line, unless we have reached
             the end of the current text fragment *)
          IF (str[pos] # 0X) OR endOfText THEN
            INC (delta, pos-lastNonWS-1)
          END;
          
          (* here holds: we are looking at an eol character; scan over the
             following whitespace, only adding CharClass.eol characters for
             the line breaks, and discarding any other whitespace *)
          WHILE (str[pos] # 0X) & LookingAtEOL (str, pos) DO
            str[pos-delta] := CharClass.eol;
            INC (pos);
            IF (str[pos] = Ascii.cr) & (str[pos+1] = Ascii.lf) THEN
              INC (pos); INC (delta)
            END;
            
            (* discard any non-eol whitespace *)
(*OBSOLETE            WHILE (str[pos] <= " ") & ~LookingAtEOL (str, pos) DO
              INC (pos); INC (delta)
            END*)
          END
        END;
        str[pos-delta] := 0X;
        
(*Out.String ("<OUTPUT_STRING>");
Out.String (str^);
Out.String ("</OUTPUT_STRING>"); Out.Ln;*)
        
        (* now that the hard work is done, scan through the simplified string,
           looking for paragraph separator and em-dash token *)
        pos := 0; start := 0;
        WHILE (str[pos] # 0X) DO
          IF (str[pos] = "-") & 
             (str[pos+1] = "-") &
             (str[pos+2] = "-") THEN
            Append (NewFragment (GetString (str^, start, pos), -1, -1, -1));
            Append (NewCommand (cmdEmDash, -1, -1, -1));
            INC (pos, 3);
            INC (start, 3)
          ELSIF (str[pos] = CharClass.eol) & (str[pos+1] = CharClass.eol) THEN
            Append (NewFragment (GetString (str^, start, pos+1), -1, -1, -1));
            Append (NewCommand (cmdParagraphSep, -1, -1, -1));
            WHILE (str[pos] = CharClass.eol) DO
              INC (pos)
            END;
            start := pos
          ELSE
            INC (pos)
          END
        END;
        IF (pos # start) THEN
          IF (start = 0) THEN
            Append (NewFragment (str, textPos+sym. pos, textLine, textColumn))
          ELSE
            Append (NewFragment (GetString (str^, start, pos), -1, -1, -1))
          END
        END
      END
    END AppendText;
  
  PROCEDURE MarkStartOfText;
    BEGIN
      textPos := pos;
      textLine := currLine;
      textColumn := pos-currLinePos+currLineTab
    END MarkStartOfText;
  
  PROCEDURE Newline (incr: LONGINT);
    VAR
      lines: LONGINT;
    BEGIN
      lines := 1;
      IF (str[pos+incr] = str[pos]) &
         ((incr = 1) OR (str[pos+incr+1] = str[pos+1])) THEN
        (* newline is actually two hard line breaks: attach the paragraph
           separator to the current line *)
        incr := incr*2;
        lines := lines*2
      END;
      
      IF inLineCommand THEN
        AppendText (str, textPos, pos+incr);
        Append (NewCommand (cmdEndOfLine, pos+sym. pos, currLine, 
                            pos-currLinePos+currLineTab))
      END;
        
      INC (currLine, lines);
      currLinePos := pos+incr;
      currLineTab := 0;
      INC (pos, incr);
      
      IF inLineCommand THEN
        MarkStartOfText;
        inLineCommand := FALSE
      END
    END Newline;
  
  PROCEDURE IsItemize (token: TextElement): BOOLEAN;
    BEGIN
      RETURN (token # NIL) & (token IS Token) & 
             (token(Token). cmdId = cmdItemize)
    END IsItemize;
  
  BEGIN
    noerr := TRUE; seqHead := NIL; seqTail := NIL;
    pos := 0; inLineCommand := FALSE; tableCommand := FALSE;
    str := Decoration.Remove (sym, decoration);

    currLine := sym. line; currLinePos := -sym. column; currLineTab := 0;
    MarkStartOfText;
    
    WHILE (str[pos] # 0X) DO
      CASE str[pos] OF
      | "@":                             (* Texinfo command *)
        AppendText (str, textPos, pos);
        INC (pos);
        
        (* copy command name into `name' *)
        IF CharClass.IsLetter (str[pos]) THEN  (* alphabetic command name *)
          i := 0;
          REPEAT
            IF (i < (LEN (name)-1)) THEN
              name[i] := str[pos];
              INC (i)
            END;
            INC (pos)
          UNTIL ~CharClass.IsLetter (str[pos]);
          len := i;
          name[i] := 0X
        ELSE  (* non-alphabetic command name: a single character *)
          name[0] := str[pos];
          name[1] := 0X;
          len := 1;
          INC (pos)
        END;

        (* ok, I am lazy: linear search for command is not the fastest
           thing to do, if the list of commands gets longer *)
        i := class4High;
        WHILE (i >= 0) & (cmdList[i]. name # name) DO
          DEC (i)
        END;
        IF (i < 0) THEN
          Error (pos-i, "Unknown Texinfo command @", name, "");
          IF (str[pos] = "{") THEN       (* skip any following "{" *)
            INC (pos)
          END
        ELSE                             (* valid command name *)
          CASE i OF
          | class1Low..class1High:       (* no arguments *)
            Append (NewCommand (i, pos+sym. pos, currLine, 
                                pos-currLinePos+currLineTab))
          | class2Low..class2High:       (* empty argument list *)
            IF (str[pos] # "{") & IsItemize (seqTail) THEN
              Append (NewCommand (i, pos+sym. pos, currLine, 
                                  pos-currLinePos+currLineTab));
            ELSIF ((str[pos] # "{") OR (str[pos+1] # "}")) THEN
              Error (pos, "Require empty argument list {} after command @",
                     cmdList[i]. name, "")
            ELSE
              Append (NewCommand (i, pos+sym. pos, currLine, 
                                  pos-currLinePos+currLineTab));
              INC (pos, 2)               (* skip "{}" *)
            END
          | class3Low..class3High:       (* need argument list *)
            IF tableCommand THEN
              IF (str[pos] = "{") THEN
                Error (pos, "Don't use braces after item format", "", "")
              END;
              Append (NewCommand (i, pos+sym. pos, currLine, 
                                  pos-currLinePos+currLineTab))
            ELSIF (str[pos] # "{") THEN
              Error (pos, "Require argument list after command @",
                     cmdList[i]. name, "")
            ELSE
              INC (pos);                 (* skip "{" *)
              Append (NewCommand (i, pos+sym. pos, currLine, 
                                  pos-currLinePos+currLineTab))
            END
          | class4Low..class4High:       (* rest of line is argument *)
            IF ~BeginningOfLine (str, pos-len-1) THEN
              Error (pos-len-1, "Command @",
                     cmdList[i]. name, " must be at beginning of line")
            END;
            Append (NewCommand (i, pos+sym. pos, currLine, 
                                pos-currLinePos+currLineTab));
            WHILE (str[pos] = " ") DO  (* skip whitespace after line cmd *)
              INC (pos)
            END;
            inLineCommand := TRUE
          END;
          tableCommand := (i = cmdTable)
        END;
        MarkStartOfText
        
      | "{":                             (* misplaced left brace *)
        Error (pos, "Misplaced {", "", "");
        INC (pos)
        
      | "}":                             (* end of argument list {..} *)
        AppendText (str, textPos, pos);
        Append (NewCommand (cmdEndOfBrace, pos+sym. pos, currLine, 
                            pos-currLinePos+currLineTab));
        INC (pos);
        MarkStartOfText
        
      | Ascii.ht:                        (* horizontal tabulator *)
        currColumn := pos-currLinePos+currLineTab;
        INC (currLineTab, S.tabWidth-currColumn MOD S.tabWidth-1);
        INC (pos)
        
      | Ascii.lf:                        (* end of line, Unix style *)
        Newline (1)
        
      | Ascii.cr:
        IF (str[pos+1] = Ascii.lf) THEN  (* end of line, DOS style *)
          Newline (2)
        ELSE                             (* end of line, Mac style *)
          Newline (1)
        END
        
      ELSE
        INC (pos)
      END
    END;
    AppendText (str, textPos, pos);
    Append (NewCommand (cmdEndOfText, pos+sym. pos, currLine, 
                        pos-currLinePos+currLineTab));
    
    IF noerr THEN
      NEW (texinfo);
      texinfo. text := sym;
      texinfo. textElements := seqHead;
      texinfo. decoration := decoration;
      RETURN texinfo
    ELSE
      RETURN NIL
    END
  END Tokenize;

PROCEDURE Append (VAR list: TextElement; elem: TextElement);
  VAR
    ptr: TextElement;
  BEGIN
    elem. nextElement := NIL;
    IF (list = NIL) THEN
      elem. prevElement := NIL;
      list := elem
    ELSE
      ptr := list;
      WHILE (ptr. nextElement # NIL) DO
        ptr := ptr. nextElement
      END;
      ptr. nextElement := elem;
      elem. prevElement := ptr
    END
  END Append;

PROCEDURE Remove (VAR list: TextElement; ptr: TextElement);
  BEGIN
    IF (ptr. nextElement # NIL) THEN
      ptr. nextElement. prevElement := ptr. prevElement
    END;
    IF (ptr = list) THEN
      list := ptr. nextElement
    ELSE
      ptr. prevElement. nextElement := ptr. nextElement
    END;
    ptr. nextElement := NIL;
    ptr. prevElement := NIL
  END Remove;

PROCEDURE Last (list: TextElement): TextElement;
  BEGIN
    IF (list = NIL) THEN
      RETURN NIL
    ELSE
      WHILE (list. nextElement # NIL) DO
        list := list. nextElement
      END;
      RETURN list
    END
  END Last;


PROCEDURE WriteElements (list, end: TextElement);
  PROCEDURE WriteElement (te: TextElement);
    BEGIN
      WITH te: Block DO  (* no code for List ... *)
        IF (te. start = NIL) THEN
          Out.String ("<p")
        ELSE
          Out.String ("<block");
          Out.String (" name='");
          Out.String (cmdList[te. start. cmdId]. name);
          Out.String ("'")
        END;
        IF te. padBefore THEN
          Out.String (" pad_before='yes'")
        END;
        IF te. padAfter THEN
          Out.String (" pad_after='yes'")
        END;
        Out.String (">");
        IF (te. lineArgs # NIL) THEN
          Out.String ("<line_args>");
          WriteElements (te. lineArgs, NIL);
          Out.String ("</line_args>");
        END;
        WriteElements (te. content, NIL);
        IF (te. start = NIL) THEN
          Out.String ("</p>")
        ELSE
          Out.String ("</block>")
        END
      | te: MarkedText DO
        Out.String ("<marked name='");
        Out.String (cmdList[te. cmdId]. name);
        Out.String ("'>");
        WriteElements (te. content, NIL);
        Out.String ("</marked>")
      | te: Token DO
        CASE te. cmdId OF 
        | cmdTextFragment:
          Out.String (te. string^)
        | cmdEmDash:
          Out.String ("<em_dash/>")
        | cmdParagraphSep:
          Out.String ("<paragraph/>")
        ELSE
          Out.String ("<command name='");
          Out.String (cmdList[te. cmdId]. name);
          Out.String ("'/>")
        END
      END
    END WriteElement;

  BEGIN
    WHILE (list # end) DO
      WriteElement (list);
      list := list. nextElement
    END
  END WriteElements;

PROCEDURE WriteTexinfo (texinfo: Texinfo);
  BEGIN
    IF (texinfo. content # NIL) THEN
      Out.String ("------------------------------------------------------------------------"); Out.Ln;
      WriteElements (texinfo. content, NIL); Out.Ln;
      Out.String ("------------------------------------------------------------------------"); Out.Ln;
    ELSE
      Out.String ("ERROR: no parsed texinfo text available"); Out.Ln
    END
  END WriteTexinfo;

PROCEDURE AllWhitespace (VAR str: ARRAY OF CHAR): BOOLEAN;
  VAR
    i: LONGINT;
  BEGIN
    i := 0;
    WHILE (str[i] # 0X) DO
      IF (str[i] > " ") THEN RETURN FALSE END;
      INC (i)
    END;
    RETURN TRUE
  END AllWhitespace;

PROCEDURE NormalizeList (block: Block; list: TextElement);
  PROCEDURE Normalize (te: TextElement);
    VAR
      s, ns: S.String;
      i, delta, dotExt: LONGINT;
      last: TextElement;

    PROCEDURE StripHeadWS (elem: TextElement);
      VAR
        i: LONGINT;
      BEGIN
        IF (elem # NIL) THEN
          WITH elem: Block DO
            (* ignore *)
          | elem: MarkedText DO
            StripHeadWS (elem. content)
          | elem: Token DO
            IF (elem. cmdId = cmdTextFragment) THEN
              i := 0;
              WHILE (elem. string[i] # 0X) & (elem. string[i] <= " ") DO
                INC (i)
              END;
              Strings.Delete (elem. string^, 0, SHORT (i))
            END
          END
        END
      END StripHeadWS;

    PROCEDURE StripTailWS (elem: TextElement);
      VAR
        i: LONGINT;
      BEGIN
        IF (elem # NIL) THEN
          WITH elem: Block DO
            (* ignore *)
          | elem: MarkedText DO
            StripTailWS (Last (elem. content))
          | elem: Token DO
            IF (elem. cmdId = cmdTextFragment) THEN
              i := Strings.Length (elem. string^);
              WHILE (i # 0) & (elem. string[i-1] <= " ") DO
                DEC (i)
              END;
              elem. string[i] := 0X
            END
          END
        END
      END StripTailWS;

    PROCEDURE EmptyParagraph (): Block;
      VAR
        p: Block;
      BEGIN
        NEW (p);
        InitBlock (p);
        RETURN p
      END EmptyParagraph;

    BEGIN
      WITH te: Block DO
        IF (te. start = NIL) OR (te. start. cmdId # cmdExample) THEN
          NormalizeList (te, te. lineArgs);
          NormalizeList (te, te. content)
        END;
        
        IF (te. start = NIL) THEN      (* paragraph *)
          StripHeadWS (te. content);
          StripTailWS (Last (te. content))
        ELSIF (te. start. cmdId = cmdItem) THEN
          IF (te. prevElement # NIL) THEN
            (* insert empty line between two items of a list *)
            te. prevElement(Block). padAfter := TRUE
          END;
          
          (* remove padding after last element of item *)
          last := Last (te. content);
          IF (last # NIL) THEN
            last(Block). padAfter := FALSE
          END;
          
          IF (te. content = NIL) THEN
            Append (te. content, EmptyParagraph())
          END;
          IF (te. lineArgs # NIL) THEN
            StripTailWS (Last (te. lineArgs))
          END
        END
      | te: MarkedText DO
        NormalizeList (block, te. content);

        IF (te. cmdId = cmdArg) THEN
          StripHeadWS (te. content);
          StripTailWS (Last (te. content))
        END
      | te: Token DO
        IF (te. cmdId = cmdTextFragment) THEN
          (* convert <=" " to space, multiple spaces to single space; two 
             whitespaces are kept after a dot, and "dot<NL>" is converted
             to "dot<SPACE><SPACE>" *)
          s := te. string; i := 0; delta := 0; dotExt := 0;
          WHILE (s[i] # 0X) DO
            IF (s[i] <= " ") THEN
              s[i-delta] := " "; INC (i);
              WHILE (s[i] # 0X) & (s[i] <= " ") DO
                INC (i); INC (delta)
              END
            ELSIF (s[i] = ".") THEN
              s[i-delta] := s[i]; INC (i);
              IF (s[i] # 0X) & (s[i] <= " ") & 
                 (s[i+1] # 0X) & (s[i+1] <= " ") THEN
                s[i-delta] := " "; INC (i) (* keep two spaces *)
              ELSIF (s[i] = CharClass.eol) THEN
                (* dot followed by eol: convert to dot plus 2 spaces; because
                   this operation can extend the string, it is done in a
                   separate step *)
                s[i-delta] := 1X; INC (i); INC (dotExt)
              END
            ELSE
              s[i-delta] := s[i]; INC (i)
            END
          END;
          s[i-delta] := 0X;

          DEC (i, delta);
          IF (i+dotExt >= LEN (s^)) THEN
            NEW (ns, i+dotExt+1);
            te. string := ns
          ELSE
            ns := s
          END;
          WHILE (i >= 0) DO
            IF (s[i] = 1X) THEN
              ns[i+dotExt] := " ";
              DEC (dotExt);
              ns[i+dotExt] := " ";
              DEC (i)
            ELSE
              ns[i+dotExt] := s[i];
              DEC (i)
            END
          END
        END
      END
    END Normalize;

  BEGIN
    WHILE (list # NIL) DO
      Normalize (list);
      list := list. nextElement
    END
  END NormalizeList;

PROCEDURE FixExamples (list: TextElement);
  VAR
    ptr: TextElement;
  
  PROCEDURE ReplaceParagraphSep (list: TextElement);
    VAR
      ptr: TextElement;
    BEGIN
      ptr := list;
      WHILE (ptr # NIL) DO
        WITH ptr: Block DO
          ReplaceParagraphSep (ptr. content)
        | ptr: Token DO
          IF (ptr. cmdId = cmdParagraphSep) THEN
            ptr. cmdId := cmdTextFragment;
            NEW (ptr. string, 2);
            ptr. string[0] := CharClass.eol;
            ptr. string[1] := 0X
          END
        ELSE (* mh, don't actually know what else could happen here... *)
        END;
        ptr := ptr. nextElement
      END
    END ReplaceParagraphSep;
  
  BEGIN
    ptr := list;
    WHILE (ptr # NIL) DO
      WITH ptr: Block DO
        IF (ptr. start. cmdId = cmdExample) THEN
          IF (ptr. content IS Token) &
             (ptr. content(Token). cmdId = cmdTextFragment) &
             (ptr. content(Token). string[0] = CharClass.eol)THEN
            (* remove newline character after example command *)
            Strings.Delete (ptr. content(Token). string^, 0, 1)
          END;
          ReplaceParagraphSep (ptr. content)
        ELSE
          FixExamples (ptr. content)
        END
      ELSE  (* ignore anything that isn't a block *)
      END;
      ptr := ptr. nextElement
    END
  END FixExamples;
  
PROCEDURE CreateParagraphs (VAR list: TextElement);
(* Inspects all text elements, collecting sequences of inline elements into
   paragraphs.  Text fragments that only contain whitspace are discarded.  *)
  VAR
    ptr, start, end, next, prevElem: TextElement;
    nonPS: BOOLEAN;

  PROCEDURE ExtractList (VAR list: TextElement;
                         start, end: TextElement): TextElement;
  (* Remove [start..end[ from list, and returns a pointer to start.  *)
    BEGIN
      IF (start. prevElement = NIL) THEN
        list := end
      ELSE
        start. prevElement. nextElement := end
      END;
      IF (end # NIL) THEN
        end. prevElement. nextElement := NIL;
        end. prevElement := start. prevElement
      END;
      start. prevElement := NIL;
      RETURN start
    END ExtractList;

  PROCEDURE NewParagraphs (content: TextElement): Block;
    VAR
      p: Block;
      ptr, start, pList, pLast: TextElement;
    BEGIN
      pList := NIL; pLast := NIL;
      ptr := content;
      WHILE (ptr # NIL) DO
        (* skip over paragraph separators *)
        start := ptr;
        WHILE (ptr # NIL) & (ptr IS Token) &
              (ptr(Token). cmdId = cmdParagraphSep) DO
          ptr := ptr. nextElement
        END;
        IF (start # ptr) & (pLast # NIL) THEN
          (* insert empty line between two paragraphs *)
          pLast(Block). padAfter := TRUE
        END;

        IF (ptr # NIL) THEN
          start := ptr;
          WHILE (ptr # NIL) & 
                (~(ptr IS Token) OR (ptr(Token). cmdId # cmdParagraphSep)) DO
            ptr := ptr. nextElement
          END;

          NEW (p);
          InitBlock (p);
          p. content := ExtractList (content, start, ptr);
          Append (pList, p);
          pLast := p
        END
      END;
      RETURN pList(Block)
    END NewParagraphs;

  PROCEDURE InsertAfter (VAR list: TextElement; prev, newList: TextElement);
    VAR
      newEnd: TextElement;
    BEGIN
      newEnd := newList;
      WHILE (newEnd. nextElement # NIL) DO
        newEnd := newEnd. nextElement
      END;

      newList. prevElement := prev;
      IF (prev = NIL) THEN
        newEnd. nextElement := list;
        IF (list # NIL) THEN
          list. prevElement := newEnd
        END;
        list := newList
      ELSE
        newEnd. nextElement := prev. nextElement;
        IF (newEnd. nextElement # NIL) THEN
          newEnd. nextElement. prevElement := newEnd
        END;
        prev. nextElement := newList
      END
    END InsertAfter;

  BEGIN
    ptr := list;
    WHILE (ptr # NIL) DO
      next := ptr. nextElement;
      WITH ptr: Block DO
        IF (ptr. start. cmdId # cmdExample) THEN
          CreateParagraphs (ptr. content)
        END
      | ptr: Token DO
        IF (ptr. cmdId = cmdTextFragment) & AllWhitespace (ptr. string^) THEN
          Remove (list, ptr)
        END
      | ptr: MarkedText DO
        (* noop *)
      END;
      ptr := next
    END;

    ptr := list;
    WHILE (ptr # NIL) DO
      start := ptr; nonPS := FALSE;
      WHILE (ptr # NIL) & ~(ptr IS Block) DO
        nonPS := nonPS OR (ptr IS MarkedText) OR
                 (ptr(Token). cmdId # cmdParagraphSep);
        ptr := ptr. nextElement
      END;
      end := ptr;

      IF (start # end) THEN            (* non-empty sequence of tokens *)
        IF nonPS THEN
          prevElem := start. prevElement;
          InsertAfter (list, prevElem, 
                       NewParagraphs (ExtractList (list, start, end)))
        ELSE
          IF (start. prevElement # NIL) THEN
            start. prevElement(Block). padAfter := TRUE
          ELSIF (end # NIL) THEN
            end(Block). padBefore := TRUE
          END;
          start := ExtractList (list, start, end)
        END
      END;

      WHILE (ptr # NIL) & (ptr IS Block) DO
        ptr := ptr. nextElement
      END
    END
  END CreateParagraphs;

PROCEDURE Parse* (commentText: S.TextSymbol): Texinfo;
(* Parses the given comment text and returns the syntax tree as its return
   value.  Result is NIL in case of an error.  *)
  VAR
    texinfo: Texinfo;
    block: Block;
    token: Token;
    noerr: BOOLEAN;
    
  PROCEDURE Error (pos: LONGINT; msg0, msg1, msg2: ARRAY OF CHAR);
    VAR
      start: S.Symbol;
    BEGIN
      start := texinfo. text;
      WHILE (start. prev # NIL) DO
        start := start. prev
      END;
      Out.String ("In file ");
      Out.String (start(S.StartSymbol). file^);
      Out.String (": ");
      Out.Ln;
      Out.LongInt (pos, 0);
      Out.String (": ");
      Out.String (msg0);
      Out.String (msg1);
      Out.String (msg2);
      Out.Ln;
      noerr := FALSE
    END Error;

  PROCEDURE GetToken;
    BEGIN
      token := texinfo. textElements(Token);
      texinfo. textElements := token. nextElement;
      token. prevElement := NIL;
      token. nextElement := NIL;
(*Out.LongInt (token. cmdId, 0); Out.String (": ");
IF (token. string # NIL) THEN
Out.String (token. string^);
END;
Out.Ln;*)
    END GetToken;
  
  PROCEDURE ParseBlock (start: Token; itemHasArgs: BOOLEAN): Block;
    VAR 
      block: Block;
      dummy: BOOLEAN;
      
    PROCEDURE ParseMarkedText (start: Token): MarkedText;
      VAR
        mt: MarkedText;
        list: TextElement;
      
      PROCEDURE ParseArguments (cmdId: LONGINT; low, high: SHORTINT; 
                                list: TextElement; VAR argList: TextElement);
        VAR
          argCount, commaPos: LONGINT;
          ptr, next, arg: TextElement;
          
        PROCEDURE CommaPos (VAR str: ARRAY OF CHAR): LONGINT;
          VAR
            i: LONGINT;
          BEGIN
            i := 0;
            WHILE (str[i] # 0X) & (str[i] # ",") DO
              INC (i)
            END;
            IF (str[i] = 0X) THEN
              RETURN -1
            ELSE
              RETURN i
            END
          END CommaPos;
        
        PROCEDURE SplitText (old: Token; pos: LONGINT): Token;
          VAR
            token: Token;
          BEGIN
            token := NewFragment (GetString (old. string^, 0, pos), 
                                  old. pos, old. line, old. column);
            Strings.Delete (old. string^, 0, SHORT (pos)+1);
            RETURN token
          END SplitText;
        
        PROCEDURE NewArgument (content: TextElement): MarkedText;
          VAR
            mt: MarkedText;
          BEGIN
            NEW (mt);
            InitTextElement (mt);
            mt. cmdId := cmdArg;
            mt. content := content;
            RETURN mt
          END NewArgument;
        
        BEGIN
          IF (low = 1) & (high = 1) THEN
            Append (argList, NewArgument (list))
          ELSE
            argCount := 1;
            ptr := list;
            WHILE (ptr # NIL) DO
              arg := NIL;
              LOOP
                next := ptr. nextElement;
                IF ~(ptr IS Token) OR
                   (ptr(Token). cmdId # cmdTextFragment) THEN
                  Append (arg, ptr)
                ELSE  (* (ptr(Token). cmdId = cmdTextFragment) *)
                  commaPos := CommaPos (ptr(Token). string^);
                  IF (commaPos < 0) THEN
                    Append (arg, ptr)
                  ELSE
                    Append (arg, SplitText (ptr(Token), commaPos));
                    IF (argCount < high) THEN
                      EXIT
                    ELSE
                      next := ptr
                    END
                  END
                END;
                ptr := next;

                IF (ptr = NIL) THEN EXIT END
              END;
              Append (argList, NewArgument (arg));
              INC (argCount)
            END;
            IF (ptr # NIL) THEN
              Append (argList, NewArgument (ptr))
            END
          END
        END ParseArguments;
      
      BEGIN
        NEW (mt);
        InitTextElement (mt);
        mt. cmdId := start. cmdId;
        mt. content := NIL;
        GetToken;
        
        list := NIL;
        WHILE (token. cmdId < class4Low) OR
              (token. cmdId = cmdEmDash) OR
              (token. cmdId = cmdTextFragment) DO
          (* as long as there is no line command, or end of file: add token
             to list *)
          IF (token. cmdId < class3Low) OR (token. cmdId >= class4Low) THEN
            Append (list, token);
            GetToken
          ELSE  (* class 3 command *)
            Append (list, ParseMarkedText (token))
          END
        END;
        IF (token. cmdId # cmdEndOfBrace) THEN
          Error (token. pos, "Expected closing brace `}' for @", 
                 cmdList[start. cmdId]. name, "")
        ELSIF (cmdOberonModule <= start. cmdId) & 
              (start. cmdId <= cmdOberonVar) &
              ((list = NIL) OR (list. nextElement # NIL)) THEN
          Error (token. pos, "Object reference @", cmdList[start. cmdId]. name,
                 " must be a qualified identifier")
        ELSE
          ParseArguments (start. cmdId,
                          cmdList[start. cmdId]. argLow,
                          cmdList[start. cmdId]. argHigh,
                          list,
                          mt. content)
        END;
        IF (token. cmdId = cmdEndOfBrace) THEN (* skip "}" *)
          GetToken
        END;
        RETURN mt
      END ParseMarkedText;
    
    PROCEDURE ParseLineArgs (block: Block; start: Token);
      BEGIN  (* pre: start=token is a line command *)
        ASSERT (start=token);
        ASSERT ((class4Low <= start. cmdId) & (start. cmdId <= class4High));
        
        block. start := start;
        GetToken;
        LOOP
          CASE token. cmdId OF
          | cmdEndOfLine:
            GetToken;
            EXIT
          | cmdEndOfText:
            EXIT
          | class1Low..class1High, class2Low..class2High, 
            cmdParagraphSep, cmdTextFragment:
            Append (block. lineArgs, token);
            GetToken
          | class3Low..class3High:
            IF (start. cmdId = cmdTable) THEN
              Append (block. lineArgs, token);
              GetToken
            ELSE
              Append (block. lineArgs, ParseMarkedText (token))
            END
          ELSE
            Error (token. pos, "This command cannot be used here", "", "");
            GetToken
          END
        END
      END ParseLineArgs;
    
    PROCEDURE StripWSFromEnd (VAR list: TextElement; VAR strippedPS: BOOLEAN);
      VAR
        last, prev: TextElement;
      BEGIN
        IF (list # NIL) THEN
          last := list;
          WHILE (last. nextElement # NIL) DO
            last := last. nextElement
          END;
          WHILE (last # NIL) DO
            prev := last. prevElement;
            IF (last IS Token) & (last(Token). cmdId = cmdParagraphSep) THEN
              strippedPS := TRUE;
              Remove (list, last)
            ELSIF (last IS Token) & (last(Token). cmdId = cmdTextFragment) &
                  AllWhitespace (last(Token). string^) THEN
              Remove (list, last)
            ELSE
              RETURN
            END;
            last := prev
          END
        END
      END StripWSFromEnd;
    
    PROCEDURE RemoveTrailingNL (block: Block; VAR list: TextElement);
      VAR
        last: TextElement;
      BEGIN
        IF (list # NIL) THEN
          last := list;
          WHILE (last. nextElement # NIL) DO
            last := last. nextElement
          END;
          IF (last IS Token) & (last(Token). cmdId = cmdParagraphSep) THEN
            block. padAfter := TRUE;
            Remove (list, last)
          END
        END;
      END RemoveTrailingNL;

    PROCEDURE CheckEndOfBlock (block: Block; start: Token);
      VAR
        endToken: Token;
        endBlock: Block;
      
      PROCEDURE Match (VAR text, pattern: ARRAY OF CHAR): BOOLEAN;
      (* Returns TRUE iff `pattern' is a prefix of `text', and the rest of
         `test' is nothing but whitespace.  *)
        VAR
          pos: INTEGER;
          diff: BOOLEAN;
        BEGIN
          Strings.FindDiff (text, pattern, diff, pos);
          IF diff & (pattern[pos] = 0X) THEN
            diff := FALSE;
            WHILE (text[pos] # 0X) DO
              IF (text[pos] > " ") THEN
                diff := TRUE
              END;
              INC (pos)
            END
          END;
          RETURN ~diff
        END Match;
      
      BEGIN
        IF (token. cmdId # cmdEnd) THEN
          Error (token. pos, "Expected @end ", cmdList[start.cmdId]. name, "");
          GetToken
        ELSE
          NEW (endBlock);
          InitBlock (endBlock);
          endToken := token;
          ParseLineArgs (endBlock, endToken);
          
          RemoveTrailingNL (block, endBlock. lineArgs);
          
          IF (endBlock. lineArgs = NIL) OR
             (endBlock. lineArgs. nextElement # NIL) OR
             (endBlock. lineArgs(Token). cmdId # cmdTextFragment) OR
             ~Match (endBlock. lineArgs(Token). string^, 
                     cmdList[start. cmdId]. name) THEN
            Error (endToken. pos, 
                   "Expected @end ", cmdList[start. cmdId]. name, "")
          END
        END
      END CheckEndOfBlock;
    
    PROCEDURE BlockCommand (id: LONGINT): BOOLEAN;
      BEGIN
        RETURN (id = cmdItemize) OR (id = cmdPreCond) OR (id = cmdPostCond) OR
               (id = cmdNoIndent) OR (id = cmdExample) OR (id = cmdTable)
      END BlockCommand;
    
    PROCEDURE ListCommand (id: LONGINT): BOOLEAN;
      BEGIN
        RETURN (id = cmdItemize) OR (id = cmdTable)
      END ListCommand;
    
    PROCEDURE StripParagraphSep (block: Block): Block;
    (* Remove any trailing paragraph separators from the contents of the
       block.  *)
      VAR
        ptr, lastNonPS: TextElement;
      BEGIN
        ptr := block. content; lastNonPS := NIL;
        WHILE (ptr # NIL) DO
          IF ~(ptr IS Token) OR (ptr(Token). cmdId # cmdParagraphSep) THEN
            lastNonPS := ptr
          END;
          ptr := ptr. nextElement
        END;
        IF (lastNonPS = NIL) THEN
          block. content := NIL
        ELSE
          lastNonPS. nextElement := NIL
        END;
        RETURN block
      END StripParagraphSep;
    
    PROCEDURE MoveElements (VAR to, from: TextElement);
      VAR
        ptr: TextElement;
      BEGIN
        IF (to = NIL) THEN
          to := from
        ELSE
          ptr := to;
          WHILE (ptr. nextElement # NIL) DO
            ptr := ptr. nextElement
          END;
          from. prevElement := ptr;
          ptr. nextElement := from
        END;
        from := NIL
      END MoveElements;
    
    BEGIN
      NEW (block);
      InitBlock (block);
      block. start := start;
      IF (start = NIL) THEN
        block. lineArgs := NIL
      ELSE
        ParseLineArgs (block, start);
        
        (* check arguments on the line that starts the block; if we aren't
           within an itemize, move any arguments into the item block *)
        CASE start. cmdId OF
        | cmdNoIndent:
          RETURN block
        | cmdItemize:
          dummy := FALSE;
          StripWSFromEnd (block. lineArgs, dummy)
        | cmdTable:
          IF (block. lineArgs = NIL) OR
             ~(block. lineArgs IS Token) OR
             (block. lineArgs(Token). cmdId < class3Low) OR
             (block. lineArgs(Token). cmdId > class3High) THEN
            Error (block. start. pos, "Table command requires argument for item format", "", "");
            GetToken
          END;
          dummy := FALSE;
          StripWSFromEnd (block. lineArgs, dummy)
        | cmdItem:
          IF itemHasArgs THEN
            dummy := FALSE;
            StripWSFromEnd (block. lineArgs, dummy)
          ELSE
            MoveElements (block. content, block. lineArgs)
          END
        ELSE
          MoveElements (block. content, block. lineArgs)
        END
      END;
      
      LOOP
        IF (token. cmdId = cmdEndOfText) THEN
          IF (start # NIL) & (start. cmdId # cmdItem) THEN
            Error (token. pos, "Expected line @end ", 
                   cmdList[start. cmdId]. name, "")
          END;
          RETURN block
        ELSIF (start # NIL) & (start. cmdId = cmdItem) & 
              (token. cmdId = cmdItem) THEN
          (* end of item entry *)
          RETURN StripParagraphSep (block)
        ELSIF (token. cmdId = cmdEnd) THEN
          IF (start = NIL) THEN
            Error (token. pos, "Invalid line command @end", "", "");
            GetToken
          ELSIF (start. cmdId = cmdItem) THEN
            RETURN StripParagraphSep (block)
          ELSE
            CheckEndOfBlock (block, start);
            RETURN block
          END
        ELSIF (token. cmdId = cmdItem) THEN
          IF ~ListCommand (start. cmdId) THEN
            Error (token. pos, "Item outside list command", "", "")
          END;
          Append (block. content, ParseBlock (token, start. cmdId = cmdTable))
        ELSIF (class3Low <= token. cmdId) & (token. cmdId <= class3High) THEN
          Append (block. content, ParseMarkedText (token))
        ELSIF BlockCommand (token. cmdId) THEN
          Append (block. content, ParseBlock (token, FALSE))
        ELSIF (class4Low <= token. cmdId) & (token. cmdId <= class4High) THEN
          Error (token. pos, "Invalid line command @", 
                 cmdList[token. cmdId]. name, "");
          GetToken
        ELSE
          Append (block. content, token);
          GetToken
        END
      END
    END ParseBlock;
  
  BEGIN
    texinfo := Tokenize (commentText);
    
    IF (texinfo # NIL) THEN  (* no error reported by tokenizer *) 
      noerr := TRUE;
      GetToken;
      block := ParseBlock (NIL, FALSE);
      IF noerr THEN
        texinfo. content := block. content;
        FixExamples (texinfo. content);
        CreateParagraphs (texinfo. content);
        NormalizeList (NIL, texinfo. content)
(*        ;WriteTexinfo (texinfo);*)
      ELSE
        texinfo := NIL
      END
    END;
    RETURN texinfo
  END Parse;


PROCEDURE GetName* (cmdId: LONGINT; VAR name: ARRAY OF CHAR);
  BEGIN
    COPY (cmdList[cmdId]. name, name)
  END GetName;

PROCEDURE IsTexinfo* (VAR str: ARRAY OF CHAR): BOOLEAN;
(* Returns TRUE if the string `str' contains a valid Texinfo command
   string "@@foo{" or "@@bar" (for line commands).  *)
  VAR
    i, j, start: LONGINT;
    name: ARRAY 16 OF CHAR;
  BEGIN
    i := 0;
    WHILE (str[i] # 0X) DO
      IF (str[i] = "@") THEN
        INC (i); start := i;
        WHILE ("a" <= str[i]) & (str[i] <= "z") DO
          INC (i)
        END;
        IF (str[i] = "{") THEN
          Strings.Extract (str, SHORT (start), SHORT (i-start), name);
          j := 0;
          WHILE (j <= class3High) & (cmdList[j]. name # name) DO
            INC (j)
          END;
          IF (j <= class4High) THEN
            RETURN TRUE
          END
        ELSIF (str[i] <= " ") THEN
          Strings.Extract (str, SHORT (start), SHORT (i-start), name);
          j := class4Low;
          WHILE (j <= class4High) & (cmdList[j]. name # name) DO
            INC (j)
          END;
          IF (j <= class4High) THEN
            RETURN TRUE
          END
        END
      END;
      INC (i)
    END;
    RETURN FALSE
  END IsTexinfo;


PROCEDURE Init;
  VAR
    i: LONGINT;
  BEGIN
    FOR i := 0 TO 255 DO
      class1[i] := -1
    END;
    FOR i := 0 TO class4High DO
      cmdList[i]. class := -1;
      cmdList[i]. name := ""
    END;
    NEW (emptyString, 1);
    emptyString[0] := 0X
  END Init;

PROCEDURE Register (cmdId: LONGINT; name: ARRAY OF CHAR);
  BEGIN
    IF (cmdList[cmdId]. class = -1) THEN
      cmdList[cmdId]. argLow := -1;
      cmdList[cmdId]. argHigh := -1;
      CASE cmdId OF
      | class1Low..class1High:
        cmdList[cmdId]. class := 1;
        ASSERT (name[1] = 0X);
        ASSERT (cmdId < MAX (SHORTINT));
        class1[ORD (name[0])] := SHORT (SHORT (cmdId))
      | class2Low..class2High:
        cmdList[cmdId]. class := 2
      | class3Low..class3High:
        cmdList[cmdId]. class := 3;
        cmdList[cmdId]. argLow := 1;
        cmdList[cmdId]. argHigh := 1
      | class4Low..class4High:
        cmdList[cmdId]. class := 4
      END;
      COPY (name, cmdList[cmdId]. name);
      ASSERT (name = cmdList[cmdId]. name)
    ELSE
      Out.String ("Module CNTexinfo: Command id ");
      Out.LongInt (cmdId, 0);
      Out.String (" for @");
      Out.String (name);
      Out.String (" already in use by @");
      Out.String (cmdList[cmdId]. name);
      Out.Ln;
      HALT(1)
    END
  END Register;

PROCEDURE RegisterArgs (cmdId: LONGINT; low, high: SHORTINT);
  BEGIN
    cmdList[cmdId]. argLow := low;
    cmdList[cmdId]. argHigh := high
  END RegisterArgs;

BEGIN
  Init;
  (* class 1 *)
  Register (cmdAtGlyph, "@");
  Register (cmdLeftBrace, "{");
  Register (cmdRightBrace, "}");
  (* class 2 *)
  Register (cmdBullet, "bullet");
  Register (cmdDots, "dots");
  Register (cmdMinus, "minus");
  Register (cmdResult, "result");
  (* class 3 *)
  Register (cmdArg, " arg");             (* pseudo command *)
  Register (cmdAsis , "asis");
  Register (cmdCite, "cite");
  Register (cmdCode, "code");
  Register (cmdDfn , "dfn");
  Register (cmdEmail, "email"); RegisterArgs (cmdEmail, 1, 2);
  Register (cmdEmph, "emph");
  Register (cmdFile, "file");
  Register (cmdKbd, "kbd");
  Register (cmdOberonModule, "omodule");
  Register (cmdOberonConst, "oconst");
  Register (cmdOberonField, "ofield");
  Register (cmdOberonParam, "oparam");
  Register (cmdOberonProc, "oproc");
  Register (cmdOberonType, "otype");
  Register (cmdOberonVar, "ovar");
  Register (cmdSamp, "samp");
  Register (cmdStrong, "strong");
  Register (cmdUref, "uref"); RegisterArgs (cmdUref, 1, 3);
  Register (cmdUrl, "url");
  Register (cmdVar, "var");
  (* class 4 *)
  Register (cmdEnd, "end");
  Register (cmdExample, "example");
  Register (cmdItem, "item");
  Register (cmdItemize, "itemize");
(*  Register (cmdItemX, "itemx");*)
  Register (cmdNoIndent, "noindent");
  Register (cmdPreCond, "precond");
  Register (cmdPostCond, "postcond");
  Register (cmdTable, "table");
END CNTexinfo.
