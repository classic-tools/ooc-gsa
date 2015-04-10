(*	$Id: LocStrings.Mod,v 1.3 1999/09/02 13:37:34 acken Exp $	*)
MODULE LocStrings [FOREIGN "C"; LINK FILE "LocStrings.c" END];
(* LocStrings - Character and string localization facilities.
   Copyright (C) 1996, 1997 Michael Griebling
  
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


PROCEDURE IsAlpha* (ch: CHAR): BOOLEAN;
(* return TRUE iff `ch' is alphabetic *)

PROCEDURE IsAlphaNumeric* (ch: CHAR): BOOLEAN;
(* return TRUE iff `ch' is alphabetic or a digit *)

PROCEDURE IsControl* (ch: CHAR): BOOLEAN;
(* return TRUE iff `ch' is a control character *)

PROCEDURE IsDigit* (ch: CHAR): BOOLEAN;
(* return TRUE iff `ch' is a digit *)

PROCEDURE IsGraphic* (ch: CHAR): BOOLEAN;
(* return TRUE iff `ch' is a graphical character *)

PROCEDURE IsPrintable* (ch: CHAR): BOOLEAN;
(* return TRUE iff `ch' is a printable character *)

PROCEDURE IsLower* (ch: CHAR): BOOLEAN;
(* return TRUE iff `ch' is a lowercase character *)

PROCEDURE IsPunctuation* (ch: CHAR): BOOLEAN;
(* return TRUE iff `ch' is a punctuation character *)

PROCEDURE IsSpace* (ch: CHAR): BOOLEAN;
(* return TRUE iff `ch' is a white-space character *)

PROCEDURE IsUpper* (ch: CHAR): BOOLEAN;
(* return TRUE iff `ch' is an uppercase character *)

PROCEDURE ToUpper* (ch: CHAR): CHAR;
(* return CAP(ch) *)

PROCEDURE ToLower* (ch: CHAR): CHAR;
(* return lowercase version of `ch' *)

PROCEDURE Cmp* (s1, s2: ARRAY OF CHAR): SHORTINT;
(* return the following results:
            s1<s2 -> -1
            s1=s2 ->  0
            s1>s2 ->  1 *)
            
PROCEDURE Equal* (s1, s2: ARRAY OF CHAR): BOOLEAN;
(* return TRUE when s1 = s2 *)

PROCEDURE Capitalize* (VAR s1: ARRAY OF CHAR);
(* applies the ToUpper function to each character of the string value in s1 *)

END LocStrings.
