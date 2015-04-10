(* 	$Id: IntArith.Mod,v 1.11 1998/02/01 13:39:54 acken Exp $	 *)
MODULE IntArith;
(*  This modules provides overflow detecting arithmetic operations.
    Copyright (C) 1995, 1996, 1998  Michael van Acken

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

(* This module implements overflow free integer arithmetic.  It's used to
   let the compiler detect and signal an overflow during constant evaluation
   (instead of raising an exeception, or, even worse, ignoring it).  
   
   The procedures assume that for signed types MIN(T)=-MAX(T)-1 holds, ie, that
   negative integers are coded as 2-complement, and that any calculation 
   evaluating to something larger than `FrontConfig.maxLongInt' is an 
   overflow.  *)

IMPORT
  StdTypes, Opc := Opcode;
  

TYPE
  DyadicOperator* = PROCEDURE (x, y: LONGINT; range: SHORTINT; VAR err: INTEGER): LONGINT;
  MonadicOperator* = PROCEDURE (x: LONGINT; range: SHORTINT; VAR err: INTEGER): LONGINT;
  
PROCEDURE Sgn (i: LONGINT): SHORTINT;
  BEGIN
    IF (i < 0) THEN
      RETURN -1
    ELSIF (i > 0) THEN
      RETURN 1
    ELSE
      RETURN 0
    END
  END Sgn;


PROCEDURE OutOfRange* (value: LONGINT; range: SHORTINT; VAR err: INTEGER): BOOLEAN;
  BEGIN
    IF (value < StdTypes.WholeMin (range)) OR 
       (value > StdTypes.WholeMax (range)) THEN
      err := 350;                        (* overflow *)
      RETURN TRUE
    ELSE
      RETURN FALSE
    END
  END OutOfRange;

PROCEDURE Includes* (range0, range1: SHORTINT): BOOLEAN;
(* TRUE iff all values of `range1' can be represented in `range0' without any 
   overflows.  *)
  BEGIN
    IF (range0 >= Opc.subclR) OR (range1 >= Opc.subclR) THEN
      RETURN (range0 >= range1)
    ELSE
      RETURN (StdTypes.WholeMin (range0) <= StdTypes.WholeMin (range1)) &
               (StdTypes.WholeMax (range1) <= StdTypes.WholeMax (range0))
    END
  END Includes;




PROCEDURE Add* (x, y: LONGINT; range: SHORTINT; VAR err: INTEGER): LONGINT;
(* Calculate `x+y'.  If the result fits into the range defined by `range' (ie, 
   one of the Opc.subclXY values), then  `err=-1'.  Otherwise the result is `1'
   and `err' is the error number (in this case, overflow).  Note that any 
   values beyond MAX(LONGINT) will be considered as overflow, even for `range=
   Opc.subclLU'.  *)
  VAR
    overflow: BOOLEAN;
  BEGIN
    overflow := FALSE;
    IF (Sgn (x) = Sgn (y)) & (x # 0) THEN  
      (* both x and y are either negative or positive *)
      IF (x > 0) THEN  (* x and y are positive *)
        overflow := (x > StdTypes.WholeMax (range)-y)
      ELSE  (* x and y are negative *)
        overflow := (x < StdTypes.WholeMin (range)-y)
      END
    END;
    IF overflow OR OutOfRange (x+y, range, err) THEN
      err := 350;                        (* overflow *)
      RETURN 1
    ELSE
      err := -1;
      RETURN x+y
    END
  END Add;

PROCEDURE Sub* (x, y: LONGINT; range: SHORTINT; VAR err: INTEGER): LONGINT;
(* Calculate `x-y'.  If the result fits into the range defined by `range' (ie, 
   one of the Opc.subclXY values), then  `err=-1'.  Otherwise the result is `1'
   and `err' is the error number (in this case, overflow).  Note that any 
   values beyond MAX(LONGINT) will be considered as overflow, even for `range=
   Opc.subclLU'.  *)
  BEGIN
    IF (y = MIN (LONGINT)) THEN
      IF (x = MAX (LONGINT)) THEN
        err := 350;
        RETURN 1
      ELSE
        RETURN Add (x+1, MAX (LONGINT), range, err)
      END
    ELSE
      RETURN Add (x, -y, range, err)
    END
  END Sub;

PROCEDURE Mult* (x, y: LONGINT; range: SHORTINT; VAR err: INTEGER): LONGINT;
(* Calculate `x*y'.  If the result fits into the range defined by `range' (ie, 
   one of the Opc.subclXY values), then  `err=-1'.  Otherwise the result is `1'
   and `err' is the error number (in this case, overflow).  Note that any 
   values beyond MAX(LONGINT) will be considered as overflow, even for `range=
   Opc.subclLU'.  *)
  VAR
    min, div: LONGINT;
  BEGIN
    err := -1;
    IF (x # 0) & (y # 0) & (x # 1) & (y # 1) THEN
      (* here holds: (x <= -1) OR (x >= 2), (y <= -1) OR (y >= 2) *)
      min := StdTypes.WholeMin (range);
      IF (x = min) OR (y = min) OR
         (Sgn (x) = Sgn (y)) & (Mult (-x, y, range, err) = min) THEN
        (* abort if `-x' and `-y' would cause an overflow, or if `x*y>0', but 
           `-(x*y)<=min' *)
        err := 350                       (* overflow *)
      ELSE  (* here holds: `-x', `-y' are valid, `x*y<0' *)
        IF (y < 0) THEN  (* make `y' positive, `x' negative *)
          y := -y; x := -x
        END;
        (* test `x*y < min' *)
        div := min DIV y;
        IF (x < div) OR (x = div) & (min MOD y > 0) THEN
          err := 350                     (* overflow *)
        END
      END
    END;
    IF (err > 0) OR OutOfRange (x*y, range, err) THEN
      RETURN 1
    ELSE
      RETURN x*y
    END
  END Mult;

PROCEDURE Div* (x, y: LONGINT; range: SHORTINT; VAR err: INTEGER): LONGINT;
(* Calculate `x DIV y'.  If the result fits into the range defined by `range' 
   (ie, one of the Opc.subclXY values), then  `err=-1'.  Otherwise the result 
   is `1' and `err' is the error number (overflow or division by zero).  Note 
   that any values beyond MAX(LONGINT) will be considered as overflow, even for
   `range=Opc.subclLU'.  
   Specification:
     x=(x div y)*y + (x mod y)
     0 <= (x mod y) < y  _or_  0 >= (x mod y) > y
     Note: x div y = ENTIER (x / y)
   This procedure implements this spec even if the present DIV only deals 
   correctly with positive values of `y'.  *)
  VAR
    min, div: LONGINT;
  BEGIN
    err := -1;
    div := 1;
    IF (y = 0) THEN
      err := 351                         (* division by zero *)
    ELSIF (y < 0) THEN                   (* negative right side *)
      min := StdTypes.WholeMin (range);
      IF (y = min) THEN
        IF (x = min) THEN
          div := 1
        ELSE
          div := 0
        END
      ELSIF (x = min) THEN
        div := Div (-(x-y), -y, range, err)+1
      ELSE                               (* both -x and -y are valid *)
        div := Div (-x, -y, range, err)
      END
    ELSE
      div := x DIV y
    END;
    IF (err > 0) OR OutOfRange (div, range, err) THEN
      RETURN 1
    ELSE
      RETURN div
    END
  END Div;
  
PROCEDURE Mod* (x, y: LONGINT; range: SHORTINT; VAR err: INTEGER): LONGINT;
(* Calculate `x MOD y'.  If the result fits into the range defined by `range' 
   (ie, one of the Opc.subclXY values), then  `err=-1'.  Otherwise the result 
   is `1' and `err' is the error number (overflow or division by zero).  Note 
   that any values beyond MAX(LONGINT) will be considered as overflow, even for
   `range=Opc.subclLU'.  
   Specification:
     x=(x div y)*y + (x mod y)
     0 <= (x mod y) < y  _or_  0 >= (x mod y) > y
     Note: x div y = ENTIER (x / y)
   This procedure implements this spec even if the present MOD only deals 
   correctly with positive values of `y'.  *)
  VAR
    min, mod: LONGINT;
  BEGIN
    err := -1;
    mod := 1;
    IF (y = 0) THEN
      err := 351                         (* division by zero *)
    ELSIF (y < 0) THEN                   (* negative right side *)
      min := StdTypes.WholeMin (range);
      IF (y = min) THEN
        IF (x = min) THEN
          mod := 0
        ELSE
          mod := y
        END
      ELSIF (x = min) THEN
        mod := -Mod (-(x-y), -y, range, err)
      ELSE
        mod := -Mod (-x, -y, range, err)
      END
    ELSE                               (* both -x and -y are valid *)
      mod := x MOD y
    END;
    IF (err > 0) OR OutOfRange (mod, range, err) THEN
      RETURN 1
    ELSE
      RETURN mod
    END
  END Mod;
  
PROCEDURE Neg* (x: LONGINT; range: SHORTINT; VAR err: INTEGER): LONGINT;
(* Calculate `-x'.  If the result fits into the range defined by `range' (ie, 
   one of the Opc.subclXY values), then  `err=-1'.  Otherwise the result is `1'
   and `err' is the error number (in this case, overflow).  Note that any 
   values beyond MAX(LONGINT) will be considered as overflow, even for `range=
   Opc.subclLU'.  *)
  BEGIN
    RETURN Sub (0, x, range, err)
  END Neg;
  
PROCEDURE Abs* (x: LONGINT; range: SHORTINT; VAR err: INTEGER): LONGINT;
(* Calculate `ABS(x)'.  If the result fits into the range defined by `range' 
  (ie, one of the Opc.subclXY values), then  `err=-1'.  Otherwise the result is
  `1' and `err' is the error number (in this case, overflow).  Note that any 
   values beyond MAX(LONGINT) will be considered as overflow, even for `range=
   Opc.subclLU'.  *)
  BEGIN
    IF (x >= 0) THEN
      err := -1;
      RETURN x
    ELSE
      RETURN Neg (x, range, err)
    END
  END Abs;
  
PROCEDURE Ash* (x, y: LONGINT; range: SHORTINT; VAR err: INTEGER): LONGINT;
(* Calculates `ASH (x, y)'.  If the result fits into the range defined by 
   `range' (ie, one of the Opc.subclXY values), then  `err=-1'.  Otherwise the
   result is `1' and `err' is the error number (overflow).  
   Note that any values beyond MAX(LONGINT) will be considered as overflow, 
   even for `range=Opc.subclLU'.  *)
  BEGIN
    err := -1;
    WHILE (y # 0) & (err < 0) DO
      IF (y < 0) THEN
        x := Div (x, 2, range, err);
        INC (y)
      ELSE
        x := Mult (x, 2, range, err);
        DEC (y)
      END
    END;
    IF (err < 0) THEN
      RETURN x
    ELSE
      RETURN 1
    END
  END Ash;

END IntArith.
