(* 	$Id: ParamPragmas.Mod,v 1.6 1998/02/12 19:42:42 acken Exp $	 *)
MODULE ParamPragmas;
(*  Parsing and maintenance of pragmas.
    Copyright (C) 1995, 1998  Michael van Acken

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
(* 
Implements configuration file section PRAGMAS.  It has the same syntax as 
OPTIONS.  Pragmas differ from options in that they can be 
 - changed by assignments in the source code
 - new pragmas (or rather, variables) can be introduced in the source code
 - their values can be stacked and unstacked

[This module is a nice example how things can get slowly out of hand.  First
 there were just a list of pragmas.  Then the need arose to PUSH and POP the
 values of defined variables.  Then a mechanism had to be introduced to save
 and restore the current state under the assumption that no PUSH was done 
 before saving.  And finally this assumption had to be removed, since the state
 had to be saved even after an arbitrary number of PUSH operations.  Given all
 the later requirements this module should probably have been designed in a
 different way.  Too late.  It works.  I hope.  --mva]
*)

IMPORT
  Param := Parameter, Options := ParamOptions;
  
  
TYPE
  Pragma* = Options.Option;
  
  PragmaStack = POINTER TO PragmaStackDesc;
  PragmaStackDesc = RECORD
    prev: PragmaStack;
    level: INTEGER;
    optionList: Pragma
  END;
  
  PragmasSection* = POINTER TO PragmasSectionDesc;
  PragmasSectionDesc* = RECORD
    (Options.OptionsSectionDesc)
    pragmaStack: PragmaStack;
    stackLevel-: INTEGER;
  END;

  PragmaState* = RECORD  (* used by Save/Restore *)
    varList: Options.Option;
    pragmaStack: PragmaStack;
    stackLevel: INTEGER
  END;
  
VAR
  pragmas-: PragmasSection;


PROCEDURE Push*;
  BEGIN
    INC (pragmas. stackLevel)
  END Push;

PROCEDURE PrepareForModify* (opt: Options.Option);
(* Rather than stacking all defined variables, we only store those values that
   have to be restored when the stack level is left with `Pop'.  *)
  VAR
    stack: PragmaStack;
    ptr: Options.Option;
  BEGIN
    IF (pragmas. stackLevel # 0) THEN
      (* `Push' has been called at least once *)
      IF (pragmas. pragmaStack = NIL) OR 
         (pragmas. pragmaStack. level # pragmas. stackLevel) THEN
        (* there havn't been assigned variables on this stack level before *)
        NEW (stack);
        stack. prev := pragmas. pragmaStack;
        stack. level := pragmas. stackLevel;
        stack. optionList := NIL;
        pragmas. pragmaStack := stack
      ELSE
        stack := pragmas. pragmaStack
      END;
      (* check wheter `opt' is already part of the restore list *)
      ptr := stack. optionList;
      WHILE (ptr # NIL) & (ptr. name^ # opt. name^) DO
        ptr := ptr. next
      END;
      IF (ptr = NIL) THEN  (* add current value of `opt' to restore list *)
        ptr := opt. Copy();
        ptr. next := stack. optionList;
        stack. optionList := ptr
      END
    END
  END PrepareForModify;

PROCEDURE Pop*;
  VAR
    ptr, next, opt: Options.Option;
  BEGIN
    IF (pragmas. pragmaStack # NIL) &
       (pragmas. stackLevel = pragmas. pragmaStack. level) THEN
      (* revert values to the ones in the restore list *)
      ptr := pragmas. pragmaStack. optionList;
      WHILE (ptr # NIL) DO
        opt := pragmas. Find (ptr. name^);
        next := ptr. next;
        ptr. CopyValue (opt);
        ptr := next
      END;
      pragmas. pragmaStack := pragmas. pragmaStack. prev
    END;
    DEC (pragmas. stackLevel)
  END Pop;


PROCEDURE Save* (VAR state: PragmaState);
(* Stores the current pragmas and their values in a list.  *)
  VAR
    opt, new: Options.Option;
    list: Options.Option;
  
  PROCEDURE CopyStack (stack: PragmaStack): PragmaStack;
    VAR
      new: PragmaStack;
    
    PROCEDURE CopyList (list: Options.Option): Options.Option;
      VAR
        prev, new, newList: Options.Option;
      BEGIN
        newList := NIL;
        prev := NIL;
        WHILE (list # NIL) DO
          NEW (new);
          new^ := list^;
          new. next := NIL;
          IF (prev = NIL) THEN
            newList := new
          ELSE
            prev. next := new
          END;
          prev := new;
          list := list. next
        END;
        RETURN newList
      END CopyList;
    
    BEGIN
      IF (stack = NIL) THEN
        RETURN NIL
      ELSE
        NEW (new);
        new. level := stack. level;
        new. optionList := CopyList (stack. optionList);
        new. prev := CopyStack (stack. prev);
        RETURN new
      END
    END CopyStack;
  
  BEGIN
    list := NIL;
    opt := pragmas. optionList;
    WHILE (opt # NIL) DO
      new := opt. Copy();
      new. next := list;
      list := new;
      opt := opt. next
    END;
    
    state. varList := list;
    state. pragmaStack := CopyStack (pragmas. pragmaStack);
    state. stackLevel := pragmas. stackLevel
  END Save;

PROCEDURE Restore* (VAR state: PragmaState);
(* Restores the module state to the values stored in `state'.  A variable that
   isn't part of `state' is removed, otherwise its value is set to the one in 
   the list.  All push operations since `state' are undone.  *)
  VAR
    opt, optVar, next: Options.Option;
  BEGIN
    pragmas. pragmaStack := state. pragmaStack;
    pragmas. stackLevel := state. stackLevel;
    optVar := pragmas. optionList;
    WHILE (optVar # NIL) DO
      next := optVar. next;
      opt := state. varList;
      WHILE (opt # NIL) & (opt. name^ # optVar. name^) DO
        opt := opt. next
      END;
      IF (opt = NIL) THEN
        pragmas. Remove (optVar. name^)
      ELSE
        opt. CopyValue (optVar)
      END;
      optVar := next
    END;
  END Restore;


PROCEDURE Init* (undef: SHORTINT);
(* Registers the PRAGMAS section for configuration files.  `undef'
   determines how undefined option names found during parsing are handled. 
   Possible values are `undefError', `forceDefine', `ignoreUndef', or
   `acceptUndef' (all from module `Options', see there for details).  *)
  BEGIN
    pragmas. undef := undef;
    Param.AddSection ("PRAGMAS", pragmas);
  END Init;

BEGIN
  NEW (pragmas);
  pragmas. optionList := NIL;
  pragmas. pragmaStack := NIL;
  pragmas. stackLevel := 0
END ParamPragmas.
