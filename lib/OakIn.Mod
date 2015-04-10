(*	$Id: OakIn.Mod,v 1.4 1999/11/06 15:38:02 ooc-devel Exp $	*)
MODULE OakIn;

(*
    OakIn -  Text-based input of Oberon variables.       
    Copyright (C) 1997 Michael Griebling
 
    This module is free software; you can redistribute it and/or modify
    it under the terms of the GNU Lesser General Public License as 
    published by the Free Software Foundation; either version 2 of the
    License, or (at your option) any later version.
 
    This module is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Lesser General Public License for more details.
 
    You should have received a copy of the GNU Lesser General Public
    License along with this program; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

*)


(* see also [Oakwood Guidelines, revision 1A]
Module In provides a set of basic routines for formatted input of characters, 
character sequences, numbers, and names.  It assumes a standard input stream 
with a current position that can be reset to the beginning of the stream. 

State
 - Current position.  The character position in the input stream from where the
   next symbol is read.  Open (re)sets it to the beginning of the input stream.
   After reading a symbol the current position is set to the position 
   immediately after this symbol.  Before the first call to Open the current
   position is undefined.
 - Done.  Indicates the success of an input operation.  If Done is TRUE after 
   an input operation, the operation was successful and its result is valid. 
   An unsuccessful input operation sets Done to FALSE; it remains FALSE until
   the next call to Open.  In particular, Done is set to FALSE if an attempt
   is made to read beyond the end of the input stream.   

All operations (except Open) require Done=TRUE and guarantee (Done=TRUE and the
result is valid) or (Done=FALSE).  All operations except Char skip leading
blanks, tabs or end-of-line characters.

Example:
  VAR i: INTEGER; ch: CHAR; r: REAL; s, n: ARRAY 32 OF CHAR;
  ...
  In.Open;
  In.Int(i); In.Char(ch); In.Real(r); In.String(s); In.Name(n)
  
  Input stream:
        123*1.5 "abc" Mod.Proc
  
  Results:
    i=123, ch="*", r=1.5E0, s="abc", n="Mod.Proc"
*)


IMPORT
  CharClass, IntStr, LRealStr, RealStr, StdChannels, TextRider;
  
VAR
  Done-: BOOLEAN;                        (* all operations succeeded *)
  pch: CHAR;                             (* duplicate lookahead -- Pos doesn't work? *)
  full: BOOLEAN;
  reader: TextRider.Reader;


PROCEDURE Open*;
(* (Re)sets the current position to the beginning of the input stream.  Done
   indicates if the operation was successful. *)
  BEGIN
    reader:=TextRider.ConnectReader (StdChannels.stdin); full:=FALSE;
    Done:=reader#NIL
  END Open;
  
PROCEDURE Unget(ch: CHAR);
  BEGIN
    pch:=ch; full:=TRUE
  END Unget;

PROCEDURE Char* (VAR ch: CHAR);
(* Returns the character ch at the current position. *)
  BEGIN
    IF ~Done THEN RETURN END;
    IF full THEN ch:=pch; full:=FALSE
    ELSE reader. ReadChar(ch)
    END;
    Done := (reader.res = TextRider.done)
  END Char;

(* -----------------------------------------------------------------------
   NOTE: All the code below is being duplicated here at Michael van Acken's
         request.  Anyone changing this code will most likely also have to
         change TextRider and vice versa. *)
         
PROCEDURE HexDigit (ch: CHAR) : BOOLEAN;
  BEGIN
    RETURN ((ch>="0") & (ch<="9")) OR ((ch>="A") & (ch<="F"))
  END HexDigit;

PROCEDURE HexToInt (str: ARRAY OF CHAR; VAR lint: LONGINT);
(* Returns the long integer constant `lint' in the string `str' according 
   to the format:
     IntConst = digit {hexdigit}

   Note: 80000000H-FFFFFFFFH are valid inputs which map to the negative
   integers. *)
  CONST
    BASE   = 16;
    MAXPAT = 8000000H;
  VAR
    d, pos: INTEGER;
  BEGIN    
    (* accept the hexadecimal input number *)
    lint:=0; pos:=0;
    LOOP
      (* read a digit *)
      d:=ORD(str[pos]);
      IF d=0 THEN EXIT
      ELSIF CharClass.IsNumeric(CHR(d)) THEN DEC(d, ORD("0"))
      ELSE (* A-F *) DEC(d, ORD("A")-10)
      END;
      
      (* check for overflow and adjustment *)
      IF (lint>=MAXPAT*2) OR (lint<0) THEN 
        Done:=FALSE; RETURN                   (* overflow *)
      ELSIF (lint>=MAXPAT) & (d>=8) THEN 
        DEC(lint, MAXPAT*2)                   (* adjustment *)
      END;

      (* build up the number *)
      lint:=BASE*lint+d; 
      INC(pos)
    END 
  END HexToInt;

PROCEDURE SkipBlanks (VAR ch: CHAR);
  BEGIN
    REPEAT Char(ch) UNTIL ~Done OR (ch>" ")
  END SkipBlanks;
  
PROCEDURE LongInt* (VAR n: LONGINT);
(* Returns the long integer constant n at the current position according to the
   format:
     IntConst = digit {digit} | digit {hexDigit} "H". *)
  VAR
    str: ARRAY 64 OF CHAR; 
    pos: INTEGER; res: SHORTINT;
  BEGIN 
    IF ~Done THEN RETURN END;  
    SkipBlanks(str[0]); pos:=0;
    
    (* check whether the first digit is valid *)
    IF ~CharClass.IsNumeric(str[0]) THEN Done:=FALSE; RETURN END;

    (* accumulate the digits *)
    WHILE Done & HexDigit(str[pos]) DO
      INC(pos); Char(str[pos])
    END;

   (* convert to an integer *)
    IF str[pos]="H" THEN 
      str[pos]:=0X; HexToInt(str, n)  (* HexToInt sets errors internally *)
    ELSE      
      Unget(str[pos]); str[pos]:=0X; 
      IntStr.StrToInt(str, n, res);
   
      (* set errors -- if needed *)
      IF res#IntStr.strAllRight THEN Done:=FALSE END 
    END
  END LongInt;

PROCEDURE Int* (VAR n: INTEGER);
(* Returns the integer constant n at the current position according to the
   format:
     IntConst = digit {digit} | digit {hexDigit} "H". *)
  VAR
    lint: LONGINT;
  BEGIN
    IF ~Done THEN RETURN END;
    LongInt(lint);
    IF (lint>MAX(INTEGER)) OR (lint<MIN(INTEGER)) THEN Done:=FALSE
    ELSE n:=SHORT(lint)
    END    
  END Int;
  
PROCEDURE ScanReal (VAR str: ARRAY OF CHAR; double: BOOLEAN);
  VAR
    pos: INTEGER;
  BEGIN
    SkipBlanks(str[0]); pos:=0;
     
    (* read leading digits *)
    WHILE Done & CharClass.IsNumeric(str[pos]) DO
      INC(pos); Char(str[pos])
    END;
     
    (* check for reals or hexadecimals *)
    IF str[pos]="." THEN  (* fraction present *)
      (* read trailing digits *)
      REPEAT INC(pos); Char(str[pos])
      UNTIL ~Done OR ~CharClass.IsNumeric(str[pos]);
       
      (* read the exponent *)
      IF (str[pos]="E") OR (double&(str[pos]="D")) THEN
        INC(pos); Char(str[pos]);
        
        (* check for the sign *)
        IF (str[pos]#"+") & (str[pos]#"-") THEN Done:=FALSE; RETURN END;
        
        (* read exponent digits *)
        REPEAT INC(pos); Char(str[pos])
        UNTIL ~CharClass.IsNumeric(str[pos]);
        Unget(str[pos])
      ELSE Unget(str[pos])
      END
    ELSE Unget(str[pos])
    END;
    str[pos]:=0X
  END ScanReal;

PROCEDURE LongReal* (VAR n: LONGREAL);
(* Returns the long real constant n at the current position according to the 
   format:
     LongRealConst = digit {digit} ["." {digit} 
                                    [("D" | "E") ("+" | "-") digit {digit}]]. 
*) 
  VAR
    str: ARRAY 1024 OF CHAR; res: SHORTINT; 
  BEGIN
    IF ~Done THEN RETURN END; 
    ScanReal(str, TRUE);
    LRealStr.StrToReal(str, n, res);

    (* set errors -- if needed *)
    IF res#LRealStr.strAllRight THEN Done:=FALSE END    
  END LongReal;

PROCEDURE Real* (VAR n: REAL);
(* Returns the real constant n at the current position according to the format:
     RealConst = digit {digit} ["." {digit} ["E" ("+" | "-") digit {digit}]]. 
*) 
  VAR
    str: ARRAY 1024 OF CHAR; res: SHORTINT;  
  BEGIN
    IF ~Done THEN RETURN END; 
    ScanReal(str, FALSE);
    RealStr.StrToReal(str, n, res);

    (* set errors -- if needed *)
    IF res#RealStr.strAllRight THEN Done:=FALSE END    
  END Real;

PROCEDURE String* (VAR s: ARRAY OF CHAR);
(* Returns the string s at the current position according to the format:
     StringConst = '"' char {char} '"'.
   The string must not contain characters less than blank such as EOL or 
   tab. *)
  VAR
    cnt: INTEGER; quote: CHAR;
  BEGIN
    IF ~Done THEN RETURN END;
    SkipBlanks(quote);

    (* check for leading quote *)
    IF quote#'"' THEN Done:=FALSE; RETURN END;

    (* read in the characters *)
    cnt:=-1;
    REPEAT 
      INC(cnt); Char(s[cnt]);
      IF s[cnt]<" " THEN Done:=FALSE END 
    UNTIL (cnt=LEN(s)-1) OR (s[cnt]='"') OR ~Done;
    s[cnt]:=0X; (* terminate string *) 
    
    (* error if no characters were input *)
    IF cnt=0 THEN Done:=FALSE END
  END String;

PROCEDURE Name* (VAR s: ARRAY OF CHAR);
(* Returns the name s at the current position according to the file name format
   of the underlying operating system (e.g. "lib/My.Mod" under Unix). 
   Note: This implementation defines a name as  
     Name = char {char},
   where char is any character greater than blank. *)
  VAR
    cnt: INTEGER;
  BEGIN
    IF ~Done THEN RETURN END;  
    SkipBlanks(s[0]); cnt:=0;

    (* read in the characters *)
    WHILE (s[cnt]>" ") & Done & (cnt<LEN(s)-1) DO
      INC(cnt); Char(s[cnt])
    END;
    s[cnt]:=0X (* terminate string *)
  END Name;

BEGIN
  Done:=FALSE  (* using In without calling Open first won't work *)
END OakIn.
