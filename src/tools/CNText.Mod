(*	$Id: CNText.Mod,v 1.6 1999/11/29 10:01:57 ooc-devel Exp $	*)
MODULE CNText;
(*  Writes an abstract syntax tree as a plain text file.
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
  Ascii, StdChannels, TextRider,
  S := CNScanner, AST := CNAST, Texinfo := CNTexinfo, Texi2Text := CNTexi2Text;


CONST
  sizeSpaces = 32;

VAR
  h: INTEGER;
  w: TextRider.Writer;
  spaces: ARRAY sizeSpaces+1 OF CHAR;


PROCEDURE SetWriter* (writer: TextRider.Writer);
  BEGIN
    IF (writer = NIL) THEN
      w := TextRider.ConnectWriter (StdChannels.stdout)
    ELSE
      w := writer
    END
  END SetWriter;

PROCEDURE WriteSpaces* (i: LONGINT);
  VAR
    j: LONGINT;
  BEGIN
    FOR j := 0 TO (i DIV sizeSpaces)-1 DO
      w. WriteString (spaces)
    END;
    FOR j := 1 TO i MOD sizeSpaces DO
      w. WriteChar (" ")
    END
  END WriteSpaces;

PROCEDURE WriteSymbols* (module: AST.Module; start: S.StartSymbol;
                         xref, lineNum: BOOLEAN);
(* pre: relative coordinates *)
  VAR
    sym: S.Symbol;
    lineNumSize: INTEGER;
    lineNumIncr: LONGINT;

  PROCEDURE WriteLineNum (num: LONGINT);
    BEGIN
      IF lineNum THEN
        IF (num >= 0) THEN
          WHILE (num >= lineNumIncr) DO
            INC (lineNumSize);
            lineNumIncr := lineNumIncr*10
          END;
          w. WriteLInt (num, lineNumSize)
        ELSE
          WriteSpaces (lineNumSize)
        END;
        w. WriteString (": ")
      END
    END WriteLineNum;
  
  PROCEDURE FillIn (sym: S.Symbol);
    VAR
      i, line: LONGINT;
    BEGIN
      IF lineNum THEN
        line := start. Line (sym) - sym.line + 1;
        FOR i := 0 TO sym. line-1 DO
          w. WriteLn;
          WriteLineNum (line+i)
        END
      ELSE
        FOR i := 0 TO sym. line-1 DO
          w. WriteLn
        END
      END;
      
      WriteSpaces (sym. column);
    END FillIn;
  
  PROCEDURE WriteTextSym;  (* used for comments and pragmas *)
    CONST
      sizeBuffer = 1024;
    VAR
      buffer: ARRAY sizeBuffer OF CHAR;
      str: S.String;
      i, j, line: LONGINT;
    BEGIN
      line := start. Line (sym);
      
      str := sym. str; 
      IF (sym(S.TextSymbol). info # NIL) THEN
        IF (sym(S.TextSymbol). info IS Texinfo.Texinfo) THEN
          str := Texi2Text.ToString (sym(S.TextSymbol). info(Texinfo.Texinfo))
        END
      END;
      
      IF (str[0] = "(") & (str[1] = "*") & (str[2] = "*") & (str[3] # "*") THEN
        (* change comment start from "**" to "* " *)
        COPY ("(* ", buffer);
        i := 3; j := 3
      ELSE
        i := 0; j := 0
      END;
      WHILE (str[i] # 0X) DO
        IF (str[i] = Ascii.lf) OR (str[i] = Ascii.cr) THEN
          buffer[j] := 0X;
          w. WriteString (buffer);
          j := 0;
          
          w. WriteLn;
          WriteLineNum (line);
          INC (line);
          
          IF (str[i] = Ascii.cr) & (str[i+1] = Ascii.lf) THEN
            INC (i)
          END
        ELSE
          IF (j = sizeBuffer-1) THEN
            buffer[j] := 0X;
            w. WriteString (buffer);
            j := 0
          END;
          buffer[j] := str[i];
          INC (j)
        END;
        INC (i)
      END;
      buffer[j] := 0X;
      w. WriteString (buffer)
    END WriteTextSym;
  
  BEGIN
    IF lineNum THEN
      lineNumSize := 4;
      lineNumIncr := 10000
    END;
    
    WriteLineNum (1);
    sym := start. next;
    WHILE (sym # NIL) DO
      FillIn (sym);
      IF (sym. id = S.comment) OR (sym. id = S.pragma) THEN
        WriteTextSym
      ELSE
        w. WriteString (sym. str^)      
      END;
      
      sym := sym. next
    END;
    w. WriteLn
  END WriteSymbols;

BEGIN
  FOR h := 0 TO sizeSpaces-1 DO
    spaces[h] := " "
  END;
  spaces[sizeSpaces] := 0X;
  
  SetWriter (NIL)
END CNText.
