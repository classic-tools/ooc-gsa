(* 	$Id: CNTexi2HTML.Mod,v 1.8 2000/01/07 21:21:55 ooc-devel Exp $	 *)
MODULE CNTexi2HTML;
(*  Converts Texinfo text to HTML, similar to texi2html.
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
  Strings, S := CNScanner, TextBuffer := CNTextBuffer, Texinfo := CNTexinfo,
  Decoration := CNDecoration;


(* Currently, this module is mostly a copy of CNTexi2Text.  Somebody
   should do a proper job here.  Among other things, the block formatter does
   know nothing about HTML tags... *)

VAR
  replacements: ARRAY Texinfo.class2High+1 OF ARRAY 4 OF CHAR;


PROCEDURE Convert* (texinfo: Texinfo.Texinfo; 
                    indent, scrWidth, indentFirst: LONGINT): S.String;
(* Formats the Texinfo description in `texinfo', for a screen with of
   `scrWidth', using an indentation of `indent'.  The first line of a
   paragraph is indented additional `indentFirst' spaces.  *)
  VAR
    b: TextBuffer.Buffer;
    currBlock: TextBuffer.Buffer;
    
  PROCEDURE ^ConvertBlock (block: Texinfo.Block; indent, offsetFirst: LONGINT);
  
  PROCEDURE ConvertList (list, end: Texinfo.TextElement;
                         indent, offsetFirst: LONGINT);
    VAR
      ptr: Texinfo.TextElement;
    BEGIN
      ptr := list;
      WHILE (ptr # end) DO
        ConvertBlock (ptr(Texinfo.Block), indent, offsetFirst);
        ptr := ptr. nextElement
      END
    END ConvertList;

  PROCEDURE ConvertBlock (block: Texinfo.Block; indent, offsetFirst: LONGINT);
    VAR
      len: LONGINT;
      item: Texinfo.TextElement;
      
    PROCEDURE ^ConvertInline (list: Texinfo.TextElement; noFormat: BOOLEAN);

    PROCEDURE ConvertElement (cmdId: LONGINT; list: Texinfo.TextElement;
                              noFormat: BOOLEAN);
      VAR
        name: ARRAY 16 OF CHAR;
      BEGIN
        CASE cmdId OF
        | Texinfo.cmdArg, Texinfo.cmdAsis:
          ConvertInline (list, noFormat)
        | Texinfo.cmdCite, Texinfo.cmdCode, Texinfo.cmdKbd, 
          Texinfo.cmdStrong, Texinfo.cmdVar:
          (* use texinfo command name as tag *)
          Texinfo.GetName (cmdId, name);
          currBlock. Append ("<");
          currBlock. Append (name);
          currBlock. Append (">");
          ConvertInline (list, noFormat);
          currBlock. Append ("</");
          currBlock. Append (name);
          currBlock. Append (">")
        | Texinfo.cmdOberonVar, Texinfo.cmdOberonField:
          currBlock. Append ("<var>`");
          ConvertInline (list, noFormat);
          currBlock. Append ("'</var>");
        | Texinfo.cmdSamp:
          currBlock. Append ("<samp>`");
          ConvertInline (list, noFormat);
          currBlock. Append ("'</samp>");
        | Texinfo.cmdOberonModule,
          Texinfo.cmdOberonConst, Texinfo.cmdOberonProc, 
          Texinfo.cmdOberonType:
          currBlock. Append ("`");
          ConvertInline (list, noFormat);
          currBlock. Append ("'")
        | Texinfo.cmdDfn:
          currBlock. Append ('"');
          ConvertInline (list, noFormat);
          currBlock. Append ('"')
        | Texinfo.cmdEmail:
          IF (list. nextElement = NIL) THEN (* one argument *)
            currBlock. Append ("<");
            ConvertInline (list(Texinfo.MarkedText). content, noFormat);
            currBlock. Append (">")
          ELSE                       (* two arguments *)
            ConvertInline (list. nextElement, noFormat);
            currBlock. Append (" <");
            ConvertInline (list(Texinfo.MarkedText). content, noFormat);
            currBlock. Append (">")
          END
        | Texinfo.cmdEmph:
          currBlock. Append ("_");
          ConvertInline (list, noFormat);
          currBlock. Append ("_")
        | Texinfo.cmdOberonParam:
          currBlock. Append ("<var>");
          ConvertInline (list, noFormat);
          currBlock. Append ("</var>")
        | Texinfo.cmdUref:
          IF (list. nextElement = NIL) THEN (* one argument *)
            currBlock. Append ("`");
            ConvertInline (list(Texinfo.MarkedText). content, noFormat);
            currBlock. Append ("'")
          ELSIF (list. nextElement. nextElement = NIL) THEN
            ConvertInline (list. nextElement, noFormat);
            currBlock. Append (" (");
            ConvertInline (list(Texinfo.MarkedText). content, noFormat);
            currBlock. Append (")")
          ELSE                       (* three argument form *)
            ConvertInline (list. nextElement. nextElement, noFormat)
          END
        | Texinfo.cmdUrl:
          currBlock. Append ("<");
          ConvertInline (list, noFormat);
          currBlock. Append (">")
        END
      END ConvertElement;
      
    PROCEDURE ConvertInline (list: Texinfo.TextElement; noFormat: BOOLEAN);
      VAR
        ptr: Texinfo.TextElement;
        str: S.String;
        
      PROCEDURE Quote (str: S.String): S.String;
        VAR
          i, j, d: LONGINT;
          q: S.String;
        BEGIN
          i := 0; d := 0;
          WHILE (str[i] # 0X) DO
            CASE str[i] OF
            | "&": INC (d, 4)            (* &amp; *)
            | "<": INC (d, 3)            (* &lt; *)
            | ">": INC (d, 3)            (* &gt; *)
            ELSE
            END;
            INC (i)
          END;
          
          IF (d = 0) THEN
            RETURN str
          ELSE
            NEW (q, i+d+1);
            i := 0; j := 0;
            WHILE (str[i] # 0X) DO
              CASE str[i] OF
              | "&":
                q[j] := "&"; q[j+1] := "a"; q[j+2] := "m"; q[j+3] := "p";
                q[j+4] := ";";
                INC (j, 5)
              | "<": q[j] := "&"; q[j+1] := "l"; q[j+2] := "t"; q[j+3] := ";";
                INC (j, 4)
              | ">": q[j] := "&"; q[j+1] := "g"; q[j+2] := "t"; q[j+3] := ";";
                INC (j, 4)
              ELSE
                q[j] := str[i];
                INC (j)
              END;
              INC (i)
            END;
            q[j] := 0X;
            RETURN q
          END
        END Quote;
      
      BEGIN
        ptr := list;
        WHILE (ptr # NIL) DO
          WITH ptr: Texinfo.MarkedText DO
            ConvertElement (ptr. cmdId, ptr. content, noFormat)
          | ptr: Texinfo.Token DO
            CASE ptr. cmdId OF
            | Texinfo.class1Low..Texinfo.class2High:
              currBlock. Append (replacements[ptr. cmdId])
            | Texinfo.cmdEmDash:
              currBlock. Append ("--")
            | Texinfo.cmdTextFragment:
              str := Quote (ptr. string);
              IF noFormat THEN
                currBlock. Append (str^)
              ELSE
                currBlock. AppendNoLB (str^)
              END
            END
          END;
          ptr := ptr. nextElement
        END
      END ConvertInline;

    PROCEDURE IsNoIndent (te: Texinfo.TextElement): BOOLEAN;
      BEGIN
        RETURN (te # NIL) &
               (te IS Texinfo.Block) &
               (te(Texinfo.Block). start # NIL) &
               (te(Texinfo.Block). start. cmdId = Texinfo.cmdNoIndent)
      END IsNoIndent;
    
    PROCEDURE FirstItem (list: Texinfo.TextElement): Texinfo.TextElement;
      BEGIN
        WHILE (list # NIL) & 
              ~((list IS Texinfo.Block) & 
                (list(Texinfo.Block). start # NIL) &
                (list(Texinfo.Block). start. cmdId = Texinfo.cmdItem)) DO
          list := list. nextElement
        END;
        RETURN list
      END FirstItem;
    
    PROCEDURE ItemPrefix (prefix: Texinfo.TextElement): LONGINT;
      VAR
        start: LONGINT;
      BEGIN
        IF (prefix = NIL) THEN
          currBlock. Append ("* ");
          RETURN 2
        ELSE
          start := currBlock. len;
          ConvertInline (prefix, FALSE);
          currBlock. Append (" ");
          RETURN currBlock. len-start
        END
      END ItemPrefix;
    
    BEGIN
      IF block. padBefore THEN b. AppendEOL END;
      IF (block. start = NIL) THEN
        ConvertInline (block. content, FALSE);
        IF IsNoIndent (block. prevElement) & (offsetFirst > 0) THEN
          TextBuffer.FormatBlockHTML (b, currBlock, indent, scrWidth, 0)
        ELSE
          TextBuffer.FormatBlockHTML (b, currBlock, indent, scrWidth, offsetFirst)
        END;
        currBlock. Clear
      ELSE
        CASE block. start. cmdId OF
        | Texinfo.cmdItemize:
          item := FirstItem (block. content);
          INC (indent, 5);
          ConvertList (block. content, item, indent, 0);
          
          WHILE (item # NIL) DO
            IF item(Texinfo.Block). padBefore THEN b. AppendEOL END;
            IF (offsetFirst < 0) THEN
              b. AppendSpaces (3);
              len := ItemPrefix (block. lineArgs);
              ConvertList (item(Texinfo.Block). content, 
                           NIL, indent, offsetFirst-3)
            ELSE
              b. AppendSpaces (indent-2);
              len := ItemPrefix (block. lineArgs);
              ConvertList (item(Texinfo.Block). content,
                           NIL, indent, -(indent-2))
            END;
            IF item(Texinfo.Block). padAfter THEN b. AppendEOL END;
            
            item := item. nextElement
          END
        | Texinfo.cmdTable:
          item := FirstItem (block. content);
          ConvertList (block. content, item, indent, 0);
          
          WHILE (item # NIL) DO
            IF item(Texinfo.Block). padBefore THEN b. AppendEOL END;
            IF (block. lineArgs(Texinfo.Token). cmdId = Texinfo.cmdAsis) THEN
              ConvertInline (item(Texinfo.Block). lineArgs, FALSE);
            ELSE
              ConvertElement (block. lineArgs(Texinfo.Token). cmdId,
                              item(Texinfo.Block). lineArgs, FALSE)
            END;
            TextBuffer.FormatBlockHTML (b, currBlock, indent, scrWidth, 0);
            currBlock. Clear;
            ConvertList (item(Texinfo.Block). content, 
                         NIL, indent+5, 0);
            IF item(Texinfo.Block). padAfter THEN b. AppendEOL END;
            item := item. nextElement
          END
        | Texinfo.cmdNoIndent:
          (* ignore *)
        | Texinfo.cmdExample:
          ConvertInline (block. content, TRUE);
          TextBuffer.IndentBlock (b, currBlock, indent+5, block. nextElement # NIL);
          currBlock. Clear
        | Texinfo.cmdPreCond:
          b. AppendSpaces (indent);
          b. Append ("<strong>Pre-condition</strong>: ");
          ConvertList (block. content, NIL, indent, -(indent+17))
        | Texinfo.cmdPostCond:
          b. AppendSpaces (indent);
          b. Append ("<strong>Post-condition</strong>: ");
          ConvertList (block. content, NIL, indent, -(indent+18))
        END
      END;
      IF block. padAfter THEN b. AppendEOL END
    END ConvertBlock;
  
  BEGIN
    b := TextBuffer.New();
    currBlock := TextBuffer.New();
    
    ConvertList (texinfo. content, NIL, indent, indentFirst);
        
    RETURN b. str
  END Convert;

PROCEDURE ToString* (texinfo: Texinfo.Texinfo): S.String;
(* Like `Convert' above, and additionally rewrites the output text into 
   a comment that can be inserted again into the original source text.  *)
  VAR
    d: Decoration.Decoration;
    s: S.String;
  
  PROCEDURE CompensateIndentation (VAR s: ARRAY OF CHAR; len: LONGINT): BOOLEAN;
    VAR
      i: LONGINT;
    BEGIN
      i := 0;
      WHILE (i # len) DO
        IF (s[i] # " ") THEN
          RETURN FALSE
        END;
        INC (i)
      END;
      RETURN TRUE
    END CompensateIndentation;
  
  BEGIN
    d := texinfo. decoration;
    s := Convert (texinfo, d. indent, d. scrWidth, 0);
    
    s := d. Decorate (s);
    IF CompensateIndentation (s^, texinfo. text. column) THEN
      Strings.Delete (s^, 0, SHORT (texinfo. text. column))
    END;
    
    RETURN s
  END ToString;

BEGIN
  replacements[Texinfo.cmdAtGlyph] := "@";
  replacements[Texinfo.cmdLeftBrace] := "{";
  replacements[Texinfo.cmdRightBrace] := "}";
  replacements[Texinfo.cmdBullet] := "*";
  replacements[Texinfo.cmdDots] := "...";
  replacements[Texinfo.cmdMinus] := "-";
  replacements[Texinfo.cmdResult] := "=>";
END CNTexi2HTML.
