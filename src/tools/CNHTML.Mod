(*	$Id: CNHTML.Mod,v 1.12 1999/11/29 10:01:43 ooc-devel Exp $	*)
MODULE CNHTML;
(*  Converts an Oberon-2 source text into a fully hyperlinked HTML document.
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
  Ascii, Strings, IntStr, StdChannels, TextRider,
  Output := CNOutput, S := CNScanner, AST := CNAST, Decl := CNDecl,
  Texinfo := CNTexinfo, Texi2HTML := CNTexi2HTML;


CONST  (* text categories distinguished in `WriteSymbol' *)
  standard* = 0;
  keyword* = 1;
  comment = 2;
  pragma = 3;
  string = 4;
  scope* = 5;
  export* = 6;
  extra = 7;
  
CONST
  sizeSpaces = 32;

VAR
  h: INTEGER;
  w: TextRider.Writer;
  startTag*, endTag*: ARRAY extra+1, 32 OF CHAR;
  quoted: ARRAY 256 OF BOOLEAN;
  spaces: ARRAY sizeSpaces+1 OF CHAR;


PROCEDURE SetWriter* (writer: TextRider.Writer);
  BEGIN
    IF (writer = NIL) THEN
      w := TextRider.ConnectWriter (StdChannels.stdout)
    ELSE
      w := writer
    END
  END SetWriter;

PROCEDURE SetColors* (col: ARRAY OF CHAR);
  VAR
    msg: ARRAY 128 OF CHAR;
  BEGIN
    IF (col = "hilit") OR (col = "hilit19") THEN
      (* keyword: RoyalBlue *)
      startTag[keyword] := '<FONT COLOR="#4169E1">';
      endTag[keyword] := "</FONT>";

      (* comment: firebrick *)
      startTag[comment] := '<FONT COLOR="#B22222">';
      endTag[comment] := "</FONT>";

      (* pragma: ForestGreen, bold *)
      startTag[pragma] := '<FONT COLOR="#228B22"><B>';
      endTag[pragma] := "</B></FONT>";

      (* string: grey40 *)
      startTag[string] := '<FONT COLOR="#666666">';
      endTag[string] := "</FONT>";

      (* scope: Blue, bold *)
      startTag[scope] := '<FONT COLOR="#0000FF"><B>';
      endTag[scope] := "</B></FONT>";

      (* export: bold *)
      startTag[export] := '<B>';
      endTag[export] := "</B>";

      (* links of redefinition of type-bound procedure: small *)
      startTag[extra] := '<SMALL>';
      endTag[extra] := "</SMALL>"
      
    ELSIF (col = "font-lock") THEN
      (* keyword: Purple *)
      startTag[keyword] := '<FONT COLOR="#A020F0">';
      endTag[keyword] := "</FONT>";

      (* comment: firebrick *)
      startTag[comment] := '<FONT COLOR="#B22222">';
      endTag[comment] := "</FONT>";

      (* pragma: CadetBlue *)
      startTag[pragma] := '<FONT COLOR="#5F9EA0">';
      endTag[pragma] := "</FONT>";

      (* string: RosyBrown *)
      startTag[string] := '<FONT COLOR="#BC8F8F">';
      endTag[string] := "</FONT>";

      (* scope: Purple, bold *)
      startTag[scope] := '<FONT COLOR="#A020F0"><B>';
      endTag[scope] := "</B></FONT>";

      (* export: bold *)
      startTag[export] := '<B>';
      endTag[export] := "</B>";

      (* links of redefinition of type-bound procedure: small *)
      startTag[extra] := '<SMALL>';
      endTag[extra] := "</SMALL>"
      
    ELSE
      COPY ("Unknown color set `", msg);
      Strings.Append (col, msg);
      Strings.Append ("'", msg);
      Output.FatalError (msg)
    END;
    
  END SetColors;

PROCEDURE WriteText* (str: ARRAY OF CHAR);
  VAR
    i, j, start: LONGINT;
    q: ARRAY 8 OF CHAR;
  BEGIN
    i := 0;
    WHILE (str[i] # 0X) DO
      start := i;
      WHILE (str[i] # 0X) & ~quoted[ORD (str[i])] DO
        INC (i)
      END;
      IF (str[i] = 0X) & (start = 0) THEN
        w. WriteString (str)
      ELSE
        FOR j := start TO i-1 DO 
          w. WriteChar (str[j])
        END;
        IF (str[i] # 0X) THEN
          CASE str[i] OF
          | "<": q := "&lt;"
          | ">": q := "&gt;"
          | "&": q := "&amp;"
          END;
          w. WriteString (q);
          INC (i)
        END
      END
    END
  END WriteText;

PROCEDURE WriteTag* (str: ARRAY OF CHAR);
  BEGIN
    w. WriteString (str)
  END WriteTag;

PROCEDURE WriteLn*;
  BEGIN
    w. WriteLn
  END WriteLn;

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

PROCEDURE WriteSymbol (sym: S.Symbol);
  VAR
    cat: INTEGER;
  BEGIN
    IF (sym. id = S.comment) THEN
      cat := comment
    ELSIF (sym. id = S.pragma) THEN
      cat := pragma
    ELSIF (sym. id = S.string) THEN
      cat := string
    ELSIF (sym. id = S.procedure) & (sym. up # NIL) &
          (sym. up IS AST.ProcDecl) OR
          (sym. id = S. module) & (sym. up # NIL) &
          (sym. up IS AST.Module) THEN
      cat := scope
    ELSIF (sym. id = S.ident) & (sym. up # NIL) &
          (sym. up IS AST.IdentDef) & (sym. up(AST.IdentDef). mark # NIL) THEN
      cat := export
    ELSIF (sym. id # S.ident) & 
          ("A" <= sym. str[0]) & (sym. str[0] <= "Z") THEN
      cat := keyword
    ELSE
      cat := standard
    END;

    IF (cat # standard) THEN
      w. WriteString (startTag[cat])
    END;
    WriteText (sym. str^);
    IF (cat # standard) THEN
      w. WriteString (endTag[cat])
    END
  END WriteSymbol;

PROCEDURE InsertSuffix (VAR declId, suffix: ARRAY OF CHAR);
  VAR
    i: INTEGER;
  BEGIN
    IF (suffix # "") & (declId[0] # "#") THEN
      i := 0;
      WHILE (declId[i] # ".") DO
        ASSERT (declId[i] # 0X);
        INC (i)
      END;
      Strings.Insert (suffix, i, declId)
    END
  END InsertSuffix;


PROCEDURE WriteSymbols* (module: AST.Module; fileSuffix: ARRAY OF CHAR;
                         xref, lineNum: BOOLEAN);
(* pre: relative coordinates *)
  VAR
    sym: S.Symbol;
    start: S.StartSymbol;
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
  
  PROCEDURE WriteModule (node: AST.Node);
    BEGIN
      WHILE ~(node IS AST.Module) DO
        node := node. up
      END;
      WriteText (node(AST.Module). name. name. str^)
    END WriteModule;
  
  PROCEDURE WriteIdent;
    VAR
      id: ARRAY 1024 OF CHAR;
      str: ARRAY 16 OF CHAR;
    BEGIN
      Decl.DeclarationID (sym. up(AST.Ident), "_", id);
      IF (sym. up. up IS AST.Module) THEN  (* module name *)
        IF xref THEN   (* write href to xref file *)
          w. WriteString ('<A HREF="');
          WriteModule (sym);
          w. WriteString (fileSuffix);
          w. WriteString ('_xref.html">');
          WriteSymbol (sym);
          w. WriteString ('</A>');
        ELSE
          WriteSymbol (sym)
        END
      ELSIF (sym. up. up IS AST.Import) THEN
        IF (sym. up. up(AST.Import). becomes = NIL) OR
           (sym. up. up(AST.Import). module = sym. up) THEN
          w. WriteString ('<A HREF="');
          w. WriteString (sym. up(AST.Ident). name. str^);
          w. WriteString (fileSuffix);
          w. WriteString ('.html"');
          IF xref THEN
            w. WriteString (' NAME="');
            IntStr.IntToStr (sym. pos, id);
            w. WriteString (id);
            w. WriteString ('"')
          END;
          w. WriteString ('>');
          WriteSymbol (sym);  (* ... formatting inside anchor *)
          w. WriteString ("</A>")
        ELSE
          WriteSymbol (sym)
        END
      ELSIF (id # "") THEN
        IF Decl.IsDeclaration (sym. up(AST.Ident)) THEN
          (* emit anchor for defining occurence of a name *)
          w. WriteString ('<A NAME="');
          ASSERT (id[0] = "#");
          Strings.Delete (id, 0, 1);
          w. WriteString (id);
          IF xref THEN
            w. WriteString ('" HREF="');
            WriteModule (sym);
            w. WriteString (fileSuffix);
            w. WriteString ("_xref.html#");
            IntStr.IntToStr (sym. pos, str);
            w. WriteString (str)
          END;
          w. WriteString ('">')
        ELSE
          (* emit href to defining occurence of a name *)
          w. WriteString ('<A HREF="');
          InsertSuffix (id, fileSuffix);
          w. WriteString (id);
          w. WriteString ('"');
          IF xref THEN
            w. WriteString (' NAME="');
            IntStr.IntToStr (sym. pos, id);
            w. WriteString (id);
            w. WriteString ('"')
          END;
          w. WriteString ('>');
        END;
        WriteSymbol (sym);  (* ... formatting inside anchor *)
        w. WriteString ("</A>")
      ELSE
        WriteSymbol (sym)
      END;
      sym := sym. next
    END WriteIdent;
  
  PROCEDURE WriteQualident (qident: AST.Qualident);
  (* pre: sym = qident.module.name.name *)
    VAR
      id: ARRAY 1024 OF CHAR;
    
    PROCEDURE WriteNext (outputSym: AST.Symbol);
      BEGIN
        WHILE (sym # outputSym) DO
          FillIn (sym);
          WriteSymbol (sym);
          sym := sym. next
        END;
        FillIn (sym);
        WriteSymbol (sym);
        sym := sym. next
      END WriteNext;
    
    BEGIN
      Decl.DeclarationID (qident. ident, "_", id);
      IF (id # "") THEN
        w. WriteString ('<A HREF="');
        InsertSuffix (id, fileSuffix);
        w. WriteString (id);
        w. WriteString ('"');
        IF xref THEN
          w. WriteString (' NAME="');
          IntStr.IntToStr (qident. ident. name. pos, id);
          w. WriteString (id);
          w. WriteString ('"');
        END;
        w. WriteString ('>');
      END;
      
      WriteSymbol (qident. module. name);  (* ... formatting inside anchor *)
      sym := sym. next;
      WriteNext (qident. period);
      WriteNext (qident. ident. name);
      
      IF (id # "") THEN
        w. WriteString ("</A>")
      END
    END WriteQualident;
  
  PROCEDURE WriteSuperLinks (procDecl: AST.ProcDecl);
    VAR
      super, base: ARRAY 1024 OF CHAR;
    BEGIN
      Decl.ProcSuperIDs (procDecl, "_", super, base);
      IF (super # "") OR (base # "") THEN
        w. WriteString (startTag[extra]);
        IF (super # "") THEN
          w. WriteString (' <A HREF="');
          InsertSuffix (super, fileSuffix);
          w. WriteString (super);
          w. WriteString ('">SUPER</A>')
        END;
        IF (base # "") THEN
          w. WriteString (' <A HREF="');
          InsertSuffix (base, fileSuffix);
          w. WriteString (base);
          w. WriteString ('">BASE</A>')
        END;
        w. WriteString (endTag[extra])
      END
    END WriteSuperLinks;
  
  PROCEDURE WriteTextSym;  (* used for comments and pragmas *)
    CONST
      sizeBuffer = 1024;
    VAR
      cat: INTEGER;
      buffer: ARRAY sizeBuffer OF CHAR;
      str: S.String;
      i, j, line: LONGINT;
      formatted: BOOLEAN;
    BEGIN
      IF (sym. id = S.comment) THEN
        cat := comment
      ELSE (* (sym. id = S.pragma) *)
        cat := pragma
      END;
      line := start. Line (sym);
      w. WriteString (startTag[cat]);
      
      str := sym. str; formatted := FALSE;
      IF (sym(S.TextSymbol). info # NIL) THEN
        IF (sym(S.TextSymbol). info IS Texinfo.Texinfo) THEN
          str := Texi2HTML.ToString (sym(S.TextSymbol). info(Texinfo.Texinfo));
          formatted := TRUE
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
          IF formatted THEN
            WriteTag (buffer)
          ELSE
            WriteText (buffer)
          END;
          j := 0;
          
          w. WriteString (endTag[cat]);
          w. WriteLn;
          WriteLineNum (line);
          w. WriteString (startTag[cat]);
          INC (line);
          
          IF (str[i] = Ascii.cr) & (str[i+1] = Ascii.lf) THEN
            INC (i)
          END
        ELSE
          IF (j = sizeBuffer-1) THEN
            buffer[j] := 0X;
            IF formatted THEN
              WriteTag (buffer)
            ELSE
              WriteText (buffer)
            END;
            j := 0
          END;
          buffer[j] := str[i];
          INC (j)
        END;
        INC (i)
      END;
      buffer[j] := 0X;
      IF formatted THEN
        WriteTag (buffer)
      ELSE
        WriteText (buffer)
      END;
      
      w. WriteString (endTag[cat])
    END WriteTextSym;
  
  BEGIN
    IF lineNum THEN
      lineNumSize := 4;
      lineNumIncr := 10000
    END;
    start := module. startSymbol;
    
    w. WriteString ("<HTML>"); w. WriteLn;
    w. WriteString ("<HEAD>"); w. WriteLn;
    w. WriteString ("<TITLE>");
    WriteText (start. file^);
    w. WriteString ("</TITLE>"); w. WriteLn;
    w. WriteString ("</HEAD>"); w. WriteLn;
    w. WriteString ('<BODY BGCOLOR="#FFFAFA" TEXT="#000000" LINK="#000000" VLINK="#000000">'); w. WriteLn;
    w. WriteString ("<PRE>"); w. WriteLn;
    
    WriteLineNum (1);
    Decl.currModule := module;
    sym := start. next;
    WHILE (sym # NIL) DO
      FillIn (sym);
      
      IF (sym. id = S.ident) & (sym. up IS AST.Ident) THEN
        IF (sym. up. up IS AST.Qualident) & 
           (sym. up. up(AST.Qualident). module # NIL) THEN
          (* treat qualified identifier as a single entity *)
          WriteQualident (sym. up. up(AST.Qualident))
          
        ELSIF (sym. up. up IS AST.Import) & 
              (sym. up. up(AST.Import). module = sym. up) THEN
          (* add link from import clause to imported module *)
          w. WriteString ('<A HREF="');
          w. WriteString (sym. str^);
          w. WriteString (fileSuffix);
          w. WriteString ('.html">');
          WriteIdent;
          w. WriteString ("</A>")
          
        ELSE  (* identifier that is part if a qualified identifier *)
          WriteIdent
        END
        
      ELSIF (sym. id = S.semicolon) & (sym. up IS AST.ProcDecl) &
            (sym. up(AST.ProcDecl). semicolon1 = sym) &
            (sym. up(AST.ProcDecl). receiver # NIL) THEN
        (* if the type-bound procedure is a redefinition of an existing one,
           add a link the redefined procedure and to the most basic definition
           (if possible) *)
        WriteSymbol (sym);
        WriteSuperLinks (sym. up(AST.ProcDecl));
        sym := sym. next
        
      ELSIF (sym. id = S.comment) OR (sym. id = S.pragma) THEN
        WriteTextSym;
        sym := sym. next
        
      ELSE
        WriteSymbol (sym);
        sym := sym. next
      END
    END;
    w. WriteLn;
    
    w. WriteString ("</PRE>"); w. WriteLn;
    w. WriteString ("</BODY>"); w. WriteLn;
    w. WriteString ("</HTML>"); w. WriteLn
  END WriteSymbols;

BEGIN
  startTag[standard] := ""; endTag[standard] := "";
  SetColors ("hilit19");
  
  FOR h := 0 TO 255 DO quoted[h] := FALSE END;
  quoted[ORD ("<")] := TRUE;
  quoted[ORD (">")] := TRUE;
  quoted[ORD ("&")] := TRUE;
  
  FOR h := 0 TO sizeSpaces-1 DO
    spaces[h] := " "
  END;
  spaces[sizeSpaces] := 0X;
  
  SetWriter (NIL)
END CNHTML.
