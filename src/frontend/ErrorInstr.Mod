(*	$Id: ErrorInstr.Mod,v 1.5 1999/03/15 18:50:15 acken Exp $	*)
MODULE ErrorInstr;
(*  Implements error reporting for optimization phases.
    Copyright (C) 1995, 1997  Michael van Acken

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
  Param := Parameter, D := Data, E := Error;
  

PROCEDURE SetErrorEnv (ref: D.Node; VAR prev: Param.String): LONGINT;
(* Sets the error context to the module to which `ref' belongs.  `ref' has to 
   be a `Data.Opnd' or an `Data.Instruction'.  `prev' will return the old 
   error context.  *)
  VAR
    pos: LONGINT;
    greg: D.GlobalRegion;
    module: D.Object;
  BEGIN
    prev := E.sourceFile;
    IF (ref IS D.Opnd) THEN
      ref := ref(D.Opnd). instr
    END;
    WITH ref: D.Instruction DO
      pos := ref. pos;
      greg := ref. region. Greg()
    END;
    IF (greg. bodyOf = NIL) THEN
      (* overflow while parsing a constant expression in a pseudo greg; error
         refers to current source file *)
      prev := E.sourceFile
    ELSE
      module := greg. bodyOf. Module();
      (* set the error's reference file *)
      E.sourceFile := module. data(D.Const). string
    END;
    RETURN pos
  END SetErrorEnv;


PROCEDURE ErrIns2* (ref: D.Node; num: INTEGER; ins1, ins2: ARRAY OF CHAR);
(* Writes error or warning refering to `ref'.
   pre: `ref' is of the type `Data.Instruction' or `Data.Opnd', `num' a valid 
     error number (if positive), or warning number (if negative).
   post: The description of `num' is retrieved with `GetErrorMsg', if a non-
     empty `ins1' or `ins2' is is inserted into the message.  An error is 
     suppressed if it is too close to a previous ones position.  Otherwise the
     error/warning is stored in the internal list.  *)
  VAR
    prev: Param.String;
  BEGIN
    E.ErrIns2 (SetErrorEnv (ref, prev), num, ins1, ins2);
    E.sourceFile := prev
  END ErrIns2;

PROCEDURE ErrIns* (ref: D.Usable; num: INTEGER; ins: ARRAY OF CHAR);
  BEGIN
    ErrIns2 (ref, num, ins, "")
  END ErrIns;

PROCEDURE Err* (ref: D.Usable; num: INTEGER);
  BEGIN
    ErrIns2 (ref, num, "", "")
  END Err;

PROCEDURE ErrOoR* (ref: D.Node; num: INTEGER; min, maxPlusOne: LONGINT);
(* Generates an "out of range" error message.  The intervall 
   `min <= x < maxPlusOne' is inserted into the error description.  *)
  VAR
    prev: Param.String;
  BEGIN
    E.ErrOoR (SetErrorEnv (ref, prev), num, min, maxPlusOne);
    E.sourceFile := prev
  END ErrOoR;

END ErrorInstr.
