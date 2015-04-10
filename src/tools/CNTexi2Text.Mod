(* 	$Id: CNTexi2Text.Mod,v 1.5 2000/01/02 15:10:15 ooc-devel Exp $	 *)
MODULE CNTexi2Text;
(*  Converts Texinfo text to plain ASCII file, similar to makeinfo.
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
        h: LONGINT;
      BEGIN
        CASE cmdId OF
        | Texinfo.cmdArg, Texinfo.cmdAsis:
          ConvertInline (list, noFormat)
        | Texinfo.cmdCite, Texinfo.cmdCode, Texinfo.cmdKbd, 
          Texinfo.cmdSamp, 
          Texinfo.cmdOberonModule, Texinfo.cmdOberonConst,
          Texinfo.cmdOberonProc, Texinfo.cmdOberonType, 
          Texinfo.cmdOberonVar, Texinfo.cmdOberonField:
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
        | Texinfo.cmdStrong:
          currBlock. Append ("*");
          ConvertInline (list, noFormat);
          currBlock. Append ("*")
        | Texinfo.cmdVar, Texinfo.cmdOberonParam:
          h := currBlock. len;
          ConvertInline (list, noFormat);
          currBlock. Capitalize (h, currBlock. len)
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
              IF noFormat THEN
                currBlock. Append (ptr. string^)
              ELSE
                currBlock. AppendNoLB (ptr. string^)
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
          TextBuffer.FormatBlock(b, currBlock, indent, scrWidth, 0)
        ELSE
          TextBuffer.FormatBlock(b, currBlock, indent, scrWidth, offsetFirst)
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
            TextBuffer.FormatBlock(b, currBlock, indent, scrWidth, 0);
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
          b. Append ("*Pre-condition*: ");
          ConvertList (block. content, NIL, indent, -(indent+17))
        | Texinfo.cmdPostCond:
          b. AppendSpaces (indent);
          b. Append ("*Post-condition*: ");
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
END CNTexi2Text.
