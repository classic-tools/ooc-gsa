(* 	$Id: CNTexi2HTML.Mod,v 1.2 1999/11/22 21:33:41 ooc-devel Exp $	 *)
MODULE CNTexi2HTML;
(*  Converts Texinfo text to HTML, similar to texi2html.
    Copyright (C) 1999  Michael van Acken

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
   `scrWidth`, using an indentation of `indent'.  The first line of a
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
      
    PROCEDURE ConvertInline (list: Texinfo.TextElement);
      VAR
        ptr: Texinfo.TextElement;
        h: LONGINT;
        name: ARRAY 16 OF CHAR;
      BEGIN
        ptr := list;
        WHILE (ptr # NIL) DO
          WITH ptr: Texinfo.MarkedText DO
            CASE ptr. cmdId OF
            | Texinfo.cmdArg, Texinfo.cmdAsis:
              ConvertInline (ptr. content)
            | Texinfo.cmdCite, Texinfo.cmdCode, Texinfo.cmdKbd, 
              Texinfo.cmdStrong, Texinfo.cmdVar:
              (* use texinfo command name as tag *)
              Texinfo.GetName (ptr. cmdId, name);
              currBlock. Append ("<");
              currBlock. Append (name);
              currBlock. Append (">");
              ConvertInline (ptr. content);
              currBlock. Append ("</");
              currBlock. Append (name);
              currBlock. Append (">")
            | Texinfo.cmdOberonVar, Texinfo.cmdOberonField:
              currBlock. Append ("<var>`");
              ConvertInline (ptr. content);
              currBlock. Append ("'</var>");
            | Texinfo.cmdSamp:
              currBlock. Append ("<samp>`");
              ConvertInline (ptr. content);
              currBlock. Append ("'</samp>");
            | Texinfo.cmdOberonModule,
              Texinfo.cmdOberonConst, Texinfo.cmdOberonProc, 
              Texinfo.cmdOberonType:
              currBlock. Append ("`");
              ConvertInline (ptr. content);
              currBlock. Append ("'")
            | Texinfo.cmdDfn:
              currBlock. Append ('"');
              ConvertInline (ptr. content);
              currBlock. Append ('"')
            | Texinfo.cmdEmail:
              IF (ptr. content. nextElement = NIL) THEN (* one argument *)
                currBlock. Append ("<");
                ConvertInline (ptr. content(Texinfo.MarkedText). content);
                currBlock. Append (">")
              ELSE                       (* two arguments *)
                ConvertInline (ptr. content. nextElement);
                currBlock. Append (" <");
                ConvertInline (ptr. content(Texinfo.MarkedText). content);
                currBlock. Append (">")
              END
            | Texinfo.cmdEmph:
              currBlock. Append ("_");
              ConvertInline (ptr. content);
              currBlock. Append ("_")
            | Texinfo.cmdOberonParam:
              currBlock. Append ("<var>");
              ConvertInline (ptr. content);
              currBlock. Append ("</var>")
            | Texinfo.cmdUref:
              IF (ptr. content. nextElement = NIL) THEN (* one argument *)
                currBlock. Append ("`");
                ConvertInline (ptr. content(Texinfo.MarkedText). content);
                currBlock. Append ("'")
              ELSIF (ptr. content. nextElement. nextElement = NIL) THEN
                ConvertInline (ptr. content. nextElement);
                currBlock. Append (" (");
                ConvertInline (ptr. content(Texinfo.MarkedText). content);
                currBlock. Append (")")
              ELSE                       (* three argument form *)
                ConvertInline (ptr. content. nextElement. nextElement)
              END
            | Texinfo.cmdUrl:
              currBlock. Append ("<");
              ConvertInline (ptr. content);
              currBlock. Append (">")
            END
          | ptr: Texinfo.Token DO
            CASE ptr. cmdId OF
            | Texinfo.class1Low..Texinfo.class2High:
              currBlock. Append (replacements[ptr. cmdId])
            | Texinfo.cmdEmDash:
              currBlock. Append ("--")
            | Texinfo.cmdTextFragment:
              currBlock. AppendNoLB (ptr. string^)
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
          ConvertInline (prefix);
          currBlock. Append (" ");
          RETURN currBlock. len-start
        END
      END ItemPrefix;
    
    BEGIN
      IF block. padBefore THEN b. AppendEOL END;
      IF (block. start = NIL) THEN
        ConvertInline (block. content);
        IF IsNoIndent (block. prevElement) & (offsetFirst > 0) THEN
          TextBuffer.FormatBlock (b, currBlock, indent, scrWidth, 0)
        ELSE
          TextBuffer.FormatBlock (b, currBlock, indent, scrWidth, offsetFirst)
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
        | Texinfo.cmdNoIndent:
          (* ignore *)
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
