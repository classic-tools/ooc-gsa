(* 	$Id: CNDecoration.Mod,v 1.3 2000/01/07 20:59:18 ooc-devel Exp $	 *)
MODULE CNDecoration;
(*  Abstraction layer dealing with comment decorations.
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
  Ascii, CharClass, Strings, S := CNScanner;
  
  
TYPE
  Decoration* = POINTER TO DecorationDesc;
  DecorationDesc* = RECORD
    indent-: LONGINT;
    scrWidth-: LONGINT;
  END;
  
TYPE
  PlainIndent = POINTER TO PlainIndentDesc;
  PlainIndentDesc = RECORD
    (DecorationDesc)
    startOffset: LONGINT;
  END;
  
PROCEDURE Remove* (sym: S.Symbol; VAR deco: Decoration): S.String;
(* Remove any decoration and the comment delimiters from the string `sym',
   and replace CR+LF or CR end of line characters with `CharClass.eol'.  
   A description of the detected decoration variant is passed back in 
   `decoration'.  *)
  CONST
    noIndent = MAX (LONGINT);
  VAR
    str: S.String;
    i, delta, len: LONGINT;
  
  PROCEDURE GetIndent (VAR str: ARRAY OF CHAR;
                       startOfLine, indent: LONGINT): LONGINT;
  (* For the line starting at `startOfLine' in the string `str', return the
     column of the first non-whitespace character.  A result of 0 means that
     the text starts immediately, and `noIndent' that the line contains 
     nothing but whitespace.  `indent' is the indentation of the first
     character of the line, and is typically zero.  *)
    VAR
      i: LONGINT;
    BEGIN
      i := startOfLine;
      WHILE (str[i] # 0X) DO
        IF (str[i] = " ") THEN
          INC (indent)
        ELSIF (str[i] = Ascii.ht) THEN
          INC (indent, S.tabWidth - indent MOD S.tabWidth)
        ELSIF (str[i] = CharClass.eol) THEN
        ELSE
          RETURN indent
        END;
        INC (i)
      END;
      RETURN noIndent                    (* line is composed of whitespace *)
    END GetIndent;
  
  PROCEDURE GetPlainIndent (str: S.String): Decoration;
  (* Determine parameters for decoration, and remove any decoration from the
     string.  *)
    VAR
      plainIndent: PlainIndent;
      i, j, d, h, indent, len: LONGINT;
    BEGIN
      (* replace comment delimiters with whitespace *)
      ASSERT (str[0] = "(");
      str[0] := " ";
      ASSERT (str[1] = "*");
      i := 1;
      WHILE (str[i] = "*") DO
        str[i] := " ";
        INC (i)
      END;
      
      len := Strings.Length (str^);
      ASSERT (str[len-1] = ")");
      str[len-1] := " ";
      ASSERT (str[len-2] = "*");
      i := len-2;
      WHILE (*(i >= 0) &*) (str[i] = "*") DO
        str[i] := " ";
        DEC (i)
      END;
      
      (* determine minimum indentation of all lines in the string *)
      NEW (plainIndent);
      plainIndent. startOffset := sym. column-1;
      plainIndent. indent := GetIndent (str^, 0, sym. column-1);
      plainIndent. scrWidth := 80-1;
      FOR i := 0 TO len DO
        IF (str[i] = CharClass.eol) THEN
          indent := GetIndent (str^, i, 0);
          IF (indent < plainIndent. indent) THEN
            plainIndent. indent := indent
          END
        END
      END;
      IF (plainIndent. indent = noIndent) THEN
        plainIndent. indent := 0
      END;
      
      IF (plainIndent. indent > 0) THEN
        (* remove indentation from all lines of the string; do _not_ remove
           more than `plainIndent. indent' characters from the beginning of
           each line *)
        i := 0; d := 0;
        WHILE (i <= len) DO
          IF (i = 0) OR (str[i] = CharClass.eol) THEN
            IF (i # 0) THEN
              str[i-d] := CharClass.eol;
              INC (i)
            END;
            
            j := i;
            WHILE (str[j] = " ") OR (str[j] = Ascii.ht) DO
              INC (j)
            END;
            IF (j-i > plainIndent. indent) THEN (* upper bound on removal *)
              j := i+plainIndent. indent
            END;
            
            INC (d, j-i);
            i := j
          ELSE
            str[i-d] := str[i];
            INC (i)
          END
        END
      END;
      
      RETURN plainIndent
    END GetPlainIndent;
  
  BEGIN
    NEW (str, Strings.Length (sym. str^)+1);
    COPY (sym. str^, str^);
    
    (* map all end-of-line variants (CR, LF, CR+LF) to CharClass.eol *)
    i := 0; delta := 0;
    WHILE (str[i] # 0X) DO
      IF (str[i] = Ascii.cr) THEN
        str[i-delta] := CharClass.eol;
        IF (str[i+1] = Ascii.lf) THEN
          INC (i); INC (delta)
        END
      ELSIF (str[i] = Ascii.lf) THEN
        str[i-delta] := CharClass.eol
      ELSE
        str[i-delta] := str[i]
      END;
      INC (i)
    END;
    len := i-delta;
    str[len] := 0X;

    (* check if this comment's string matches any know decoration *)
    deco := NIL;
    (* [... none yet] *)
    
    (* if there is no decoration match, use the fallback decoration *)
    IF (deco = NIL) THEN
      deco := GetPlainIndent (str)
    END;
    
    RETURN str
  END Remove;

PROCEDURE (d: Decoration) Decorate* (s: S.String): S.String;
(* Given the text `s', try to decorate as described in `d'.  *)
  BEGIN
    RETURN s
  END Decorate;

PROCEDURE (d: PlainIndent) Decorate* (s: S.String): S.String;
  VAR
    s2: S.String;
    len: LONGINT;
    ins: ARRAY 4 OF CHAR;
  BEGIN
    len := Strings.Length (s^);
    NEW (s2, len+3+5);
    COPY (s^, s2^);
    
    IF (len > 0) & (s2[len-1] = CharClass.eol) THEN
      s2[len-1] := 0X
    END;
    Strings.Append ("  *)", s2^);
    
    IF (s2[d. startOffset] = " ") & (s2[d. startOffset+1] = " ") THEN
      s2[d. startOffset] := "(";
      s2[d. startOffset+1] := "*"
    ELSE
      ins := "(*x";
      ins[2] := CharClass.eol;
      Strings.Insert (ins, 0, s2^)
    END;
    
    RETURN s2
  END Decorate;

END CNDecoration.
