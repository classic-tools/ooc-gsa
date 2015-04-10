(*	$Id: GenConst.Mod,v 1.13 1999/03/15 18:55:59 acken Exp $	*)
MODULE GenConst;
(*  Produces code for constants.
    Copyright (C) 1996-1999  Michael van Acken

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
  TextRider, LRealStr, IntStr, Str := Strings,
  D := Data, StdTypes, SystemFlags, AlgebraicTransformation;
  

TYPE 
  StringList* = POINTER TO StringListDesc;
  StringListDesc = RECORD
    next-: StringList;
    value-: D.Const;
    name-: ARRAY 8 OF CHAR
  END;
  UpdateList* = POINTER TO ARRAY OF D.Instruction;
  
VAR
  stringList-: StringList;

  
PROCEDURE InsertString* (const: D.Const; VAR name: ARRAY OF CHAR);
(* Adds the string constant `const' to the list of string constants that are 
   part of the current module, and assigns a unique `name' to it.  *)
  VAR
    i: INTEGER;
    string: StringList;
  BEGIN
    string := stringList;
    i := 0;
    WHILE (string # NIL) & (string. value. string # const. string) DO
      INC (i);
      string := string. next
    END;
    IF (string = NIL) THEN
      NEW (string);
      string. next := stringList;
      string. value := const;
      IntStr.IntToStr (i, string. name);
      Str.Insert ("_c", 0, string. name);
      stringList := string
    END;
    COPY (string. name, name)
  END InsertString;

PROCEDURE InitStringList*;
(* Initialize string constant list.  *)
  BEGIN
    stringList := NIL
  END InitStringList;



PROCEDURE Char (w: TextRider.Writer; val: LONGINT; charRep: BOOLEAN);
(* If `charRep' is TRUE and `ch' is a printable ASCII code, it writes the 
   character itself, otherwise it generates an appropriate escape sequence.  
   With `charRep=FALSE' it writes the character's value as integer.  *)
  VAR
    ch: CHAR;
  BEGIN
    IF charRep THEN
      ch := CHR (val);
      IF (ch < " ") OR (ch >= 07FX) OR 
         (ch = "\") OR (ch = "?") OR (ch = "'") OR (ch = '"') THEN
      (* nonprintable characters, characters not covered by ASCII, plus some
         other characters that have special meaning in ANSI-C are written in 
         their octal representation *)
        w. WriteChar ("\");
        w. WriteChar (CHR (val DIV 64+ORD ("0")));
        w. WriteChar (CHR ((val DIV 8) MOD 8+ORD ("0")));
        w. WriteChar (CHR (val MOD 8+ORD ("0")))
      ELSE
        w. WriteChar (CHR (val))
      END
    ELSE
      w. WriteLInt (val, 0)
    END
  END Char;

PROCEDURE String8 (w: TextRider.Writer; VAR str: ARRAY OF CHAR; len: LONGINT);
(* Writes a C string constant `str'.  Characters in `str' are quoted if 
   necessary.  *)
  VAR
    i: LONGINT;
  BEGIN
    w. WriteChar ('"');
    i := 0;
    WHILE (str[i] # 0X) DO
      Char (w, ORD (str[i]), TRUE);
      INC (i)
    END;
    ASSERT (i = len);
    w. WriteChar ('"')
  END String8;

PROCEDURE String16 (w: TextRider.Writer; VAR str: ARRAY OF CHAR; len: LONGINT);
(* Writes a array constant for the LONGCHAR string constant `str'.  *)
  VAR
    i: LONGINT;
  BEGIN
    w. WriteChar ("{");
    i := 0;
    WHILE (i # len*2) DO
      w. WriteLInt (LONG (ORD(str[i]))*256+ORD(str[i+1]), 0);
      w. WriteString (",");
      INC (i, 2)
    END;
    w. WriteLInt (0, 0);
    w. WriteChar ("}")
  END String16;

PROCEDURE Boolean (w: TextRider.Writer; val: BOOLEAN);
(* TRUE is mapped to 1, FALSE to 0.  *)
  BEGIN
    IF val THEN
      w. WriteString ("1")
    ELSE
      w. WriteString ("0")
    END
  END Boolean;

PROCEDURE Int* (w: TextRider.Writer; int: LONGINT);
(* Writes the integer constant `int' as a decimal constant without any suffix.
   The smallest integer value MIN cannot be written as the negation of it's 
   absoulte value, since abs(MIN)>MAX.  Therefore the representation 
   -(-(MIN+1))-1 is used instead.  *)
  BEGIN
    IF (int = StdTypes.minLongInt) THEN
      w. WriteString ("(-");
      w. WriteLInt (-(StdTypes.minLongInt+1), 0);
      w. WriteString ("-1)")
    ELSE
      w. WriteLInt (int, 0)
    END
  END Int;

PROCEDURE Real (w: TextRider.Writer; val: LONGREAL; long: BOOLEAN);
(* Generates the ASCII representation of `val'.  With `long=TRUE' the value is
   written as LONGREAL, otherwise as REAL.  *)
  VAR
    i, prec: INTEGER;
    str: ARRAY 64 OF CHAR;
  BEGIN
    IF long THEN
      prec := 17
    ELSE
      prec := 9
    END;
    LRealStr.RealToFloat (val, prec, str);
    i := 0;
    WHILE (str[i] # 0X) & (str[i] # "E") & (str[i] # ".") DO
      INC (i)
    END;
    IF (str[i] # ".") THEN
      Str.Insert (".0", i, str)
    END;
    w. WriteString (str);
    (* LONGREAL is mapped to a double constant, REAL to a float constant: *)
    IF ~long THEN
      w. WriteChar ("F")
    END
  END Real;

PROCEDURE Set (w: TextRider.Writer; set: SET; form: SHORTINT);
(* Writes the set constant as a unsigned (long) int, hexadecimal number.  *)
  VAR
    i, j, nibble, bit: INTEGER;
    digit: BOOLEAN;
    cast: ARRAY 32 OF CHAR;
  BEGIN
    IF (form = D.strSet8) THEN
      StdTypes.BasicTypes (form, cast);
      w. WriteChar ("(");
      w. WriteString (cast);
      w. WriteString (")'\x")
    ELSE
      w. WriteString ("0x")
    END;
    digit := FALSE;
    FOR i := MAX(SET)-3 TO MIN(SET) BY -4 DO
      nibble := 0; bit := 1; j := 0;
      WHILE (j < 4) DO
        IF (i+j IN set) THEN
          INC (nibble, bit)
        END;
        bit := bit*2;
        INC (j)
      END;
      IF digit OR (nibble # 0) THEN
        IF (nibble < 10) THEN
          w. WriteChar (CHR (ORD("0") + nibble))
        ELSE
          w. WriteChar (CHR (ORD("A") - 10 + nibble))
        END;
        digit := TRUE
      END
    END;
    IF ~digit THEN
      w. WriteChar ("0")
    END;
    CASE form OF
    | D.strSet8: w. WriteChar ("'")
    | D.strSet16, D.strSet32: w. WriteChar ("U")
    | D.strSet64: w. WriteString ("ULL")
    END
  END Set;

PROCEDURE Const* (w: TextRider.Writer; const: D.Const; obj: D.Object);
(* Generates ASCII representation of the constant `c'.  If `obj' is not NIL,
   the name associated to it is used instead of the constant's value. *)
  BEGIN
    IF (obj # NIL) THEN  (* named constant *)
      w. WriteString (obj. info(SystemFlags.Info). name^)
    ELSE
      CASE const. type. form OF
      | D.strBoolean:
        Boolean (w, const. int = 1)
      | D.strChar8:
        Char (w, const. int, FALSE)
      | D.strShortInt..D.strHugeInt, D.strChar16:
        Int (w, const. int)
      | D.strReal, D.strLongReal:
        Real (w, const. real, const. type. form = D.strLongReal)
      (* ... complex const? *)
      | D.strSet8..D.strSet64:
        Set (w, const. set, const. type. form)
      | D.strStringConst8:
        String8 (w, const. string^, const. int)
      | D.strStringConst16:
        String16 (w, const. string^, const. int)
      | D.strNil:
        w. WriteString ("NULL")
      END
    END
  END Const;

PROCEDURE EmitInitialization* (w: TextRider.Writer; obj: D.Object; 
                               values: UpdateList; len: LONGINT);
(* Writes the initialization expression for the array variable `obj' using the
   constants provided by the 4th argument of the instructions in `values'.  *)
  VAR
    i, perLine, width: LONGINT;
    const: D.Usable;
    zero: D.Const;
    
  PROCEDURE NewLine;
    BEGIN
      w. WriteLn;
      w. WriteString ("  ")
    END NewLine;
  
  BEGIN
    (* decide how many elements should be put into a single line *)
    i := 0;
    WHILE (values[i] = NIL) DO
      INC (i)
    END;
    const := values[i]. NthArgument (3);
    zero := AlgebraicTransformation.GetZero (const(D.Const). type);
    CASE zero. type. form OF
    | D.strBoolean : width := 1
    | D.strChar8   : width := 5
    | D.strChar16  : width := 5
    | D.strShortInt: width := 4
    | D.strInteger : width := 6
    | D.strLongInt : width := 12
    | D.strHugeInt : width := 24
    | D.strReal, 
      D.strLongReal: width := 24
    | D.strSet8    : width := 18
    | D.strSet16   : width := 7
    | D.strSet32   : width := 11
    | D.strSet64   : width := 21
    END;
    perLine := 77 DIV (width+2);
    
    w. WriteString (" = {");
    FOR i := 0 TO len-1 DO
      IF (i MOD perLine = 0) THEN
        NewLine
      END;
      IF (values[i] = NIL) THEN
        Const (w, zero, NIL)
      ELSE
        const := values[i]. NthArgument (3);
        Const (w, const(D.Const), NIL)
      END;
      w. WriteString (", ")
    END;
    w. WriteString ("};")
  END EmitInitialization;

BEGIN
  InitStringList
END GenConst.
