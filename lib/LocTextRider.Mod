(*	$Id: LocTextRider.Mod,v 1.3 1999/09/02 13:11:04 acken Exp $	*)
MODULE LocTextRider;

(*
    LocTextRider - localized text riders.
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

IMPORT Conv:=ConvTypes, LocNumConv, LocNumStr, TextRider;

TYPE
  Reader * = POINTER TO ReaderDesc;
  ReaderDesc * = RECORD (TextRider.ReaderDesc)
  END;
  Writer * = POINTER TO WriterDesc;
  WriterDesc * = RECORD (TextRider.WriterDesc)
  END;
 
PROCEDURE (r: Reader) ReadMoney * (VAR money: LONGREAL);
(* Reads a localized money string into `money'. This method will
   work with both local and international money strings. *)
VAR
  str: ARRAY 64 OF CHAR; 
  cnt: INTEGER;
  class: Conv.ScanClass;
  state: Conv.ScanState;
BEGIN
  (* get the initial state *)
  r.ReadChar(str[0]); cnt:=1;
  LocNumConv.ScanMoney(str[0], class, state);

  (* scan for valid characters *)
  WHILE ~r.Eol() & (class#Conv.invalid) & (class#Conv.terminator) DO   
    (* get next character & state *)
    r.ReadChar(str[cnt]); INC(cnt);
    state.p(str[cnt], class, state)
  END;
  
  (* convert to a number *)
  str[cnt]:=0X; money:=LocNumConv.ValueMoney(str)
END ReadMoney;

PROCEDURE (r: Reader) ReadNumber * (VAR number: LONGREAL);
(* Reads a localized number string into `number'. *)
VAR
  str: ARRAY 64 OF CHAR; 
  cnt: INTEGER;
  class: Conv.ScanClass;
  state: Conv.ScanState;
BEGIN
  (* get the initial state *)
  r.ReadChar(str[0]); cnt:=1;
  LocNumConv.ScanNumber(str[0], class, state);

  (* scan for valid characters *)
  WHILE ~r.Eol() & (class#Conv.invalid) & (class#Conv.terminator) DO   
    (* get next character & state *)
    r.ReadChar(str[cnt]); INC(cnt);
    state.p(str[cnt], class, state)
  END;
  
  (* convert to a number *)
  str[cnt]:=0X; number:=LocNumConv.ValueNumber(str)
END ReadNumber;

PROCEDURE (w: Writer) WriteMoney * (money: LONGREAL; int: BOOLEAN);
(* Writes `money' as a localized money string when int is FALSE
   and as an international money string when int is TRUE. *)
VAR
  str: ARRAY 64 OF CHAR;
BEGIN
  LocNumStr.MoneyToStr(money, int, str); w.WriteString(str)
END WriteMoney;

PROCEDURE (w: Writer) WriteNumber * (number: LONGREAL);
(* Writes `number' as a localized number string. *)
VAR
  str: ARRAY 64 OF CHAR;
BEGIN
  LocNumStr.NumToStr(number, str); w.WriteString(str)
END WriteNumber;

END LocTextRider.
