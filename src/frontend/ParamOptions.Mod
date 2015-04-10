(* 	$Id: ParamOptions.Mod,v 1.11 1998/05/06 17:50:38 acken Exp $	 *)
MODULE ParamOptions;
(*  Parsing and maintenance of program options.
    Copyright (C) 1995, 1996, 1997  Michael van Acken

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
Implements configuration file section OPTIONS.  It contains a list of 
(name, value) pairs.

Syntax:
  options_section = "OPTIONS" option_list "END".
  option_list = [option] { ";" [option]}.
  option = [ assignment | define ].
  assignment = name ":=" value.
  define = "DEFINE" assignment.
`name' is a sequence of characters and digits, starting with a character, and 
`value' is either a string or a sequence of non-whitespace characters.
  
Example:
  OPTIONS
    optFlags := "-O2 -fomit-frame-pointer";
    includeGC := TRUE;
    gcLib := '~/gc4.4/gc.a';
    debugLevel := 5;
    
    DEFINE debug := TRUE;
    DEFINE CpuType := "Motorola"
  END

This module provides three different kinds of options: boolean, integer, and
string.  Known options are modified with "name := value", new options are 
created with "DEFINE name := value", where `name' must be a unique new name.
Definitions can be disabled (see `Init').

The program registers options by calling `CreateXXX' (where XXX is the 
appropiate type) with a name and a default value and passing the result to
the type-bound procedure `options. Add'.  The result is a pointer to the 
created option which contains the option's value typically in a field 
called `value' (or, for booleans, `true').  
*)

IMPORT
  Out, Strings, IntStr, Conv := ConvTypes, Param := Parameter;
  

CONST  (* values for parameter `undef' of procedure `Init' *)
  undefError* = 0;
  (* undefined names are errors, no new names can be defined *)
  forceDefine* = 1;
  (* new names can be declared in DEFINE section, undefined names are errors *)
  ignoreUndef* = 2;
  (* ignore undefined names, do not allow DEFINE *)
  acceptUndef* = 3;
  (* accept undefined names as implicit defines *)
  
TYPE
  Option* = POINTER TO OptionDesc;
  OptionDesc* = RECORD
    next*: Option;                         
    (* links list of defined options for a given section *)
    name-: Param.String;
    (* unique name for this option *)
  END;

  OptionsSection* = POINTER TO OptionsSectionDesc;
  OptionsSectionDesc* = RECORD
    (Param.SectionDesc)
    undef*: SHORTINT;
    (* determines how OptionsSection.Parse treats undeclared options; set by 
       `Init' *)
    optionList*: Option;
    (* list of known options *)
  END;

  (* concrete option types *)
  BooleanOption* = POINTER TO BooleanOptionDesc;
  BooleanOptionDesc* = RECORD
    (OptionDesc)
    true-: BOOLEAN
  END;
  IntegerOption* = POINTER TO IntegerOptionDesc;
  IntegerOptionDesc* = RECORD
    (OptionDesc)
    value-: LONGINT;
    lower-, upper-: LONGINT              
    (* lower and upper bounds of `value' *)
  END;
  StringOption* = POINTER TO StringOptionDesc;
  StringOptionDesc* = RECORD
    (OptionDesc)
    value-: Param.String
  END;


VAR
  options-: OptionsSection;

VAR  
  done: BOOLEAN;
  error-: ARRAY 128 OF CHAR;



PROCEDURE InitOption* (opt: Option; name: ARRAY OF CHAR);
  BEGIN
    opt. next := NIL;
    NEW (opt. name, Strings.Length (name)+1);
    COPY (name, opt. name^)
  END InitOption;

PROCEDURE (opt: Option) Write*;
(* Writes option value (_not_ the name, nor any other prefix or suffix). *)
  END Write;

PROCEDURE (opt: Option) Accept* (str: ARRAY OF CHAR): BOOLEAN;
(* If `str' is a legal value for `opt', then set `opt' to this value and return
  TRUE, otherwise set `done' and `error' accordingly and return FALSE.  *)
  END Accept;

PROCEDURE (opt: Option) Copy* (): Option;
(* Creates exact copy of `opt'.  *)
  END Copy;
  
PROCEDURE (opt: Option) CopyValue* (dest: Option);
(* Copies the value of `opt' into `dest'.  The actual type of `dest' must be
   an extension of the type of `opt'.  *)
  END CopyValue;
  

PROCEDURE (section: OptionsSection) Find* (name: ARRAY OF CHAR): Option;
(* Finds an option, result is NIL if no option `name' is defined. *)
  VAR
    opt: Option;
  BEGIN
    opt := section. optionList;
    WHILE (opt # NIL) & (opt. name^ # name) DO
      opt := opt. next
    END;
    RETURN opt
  END Find;

PROCEDURE (section: OptionsSection) Add* (option: Option);
(* Add `option' to `section's option list. 
   pre: No other option of the same name is registered in the list.  *)
  BEGIN
    option. next := section. optionList;
    section. optionList := option
  END Add;

PROCEDURE (section: OptionsSection) Remove* (name: ARRAY OF CHAR);
(* Removes option `name' from the list in `section'.
   pre: An option of that name exists. *)
  PROCEDURE Remove (VAR opt: Option);
    BEGIN
      IF (opt. name^ = name) THEN
        opt := opt. next
      ELSE
        Remove (opt. next)
      END
    END Remove;
  
  BEGIN
    Remove (section. optionList)
  END Remove;



(*
The following procedures realize concrete implementations of options.  Each
type XXX must define five procedures:
 - function CreateXXX to create an option of a given name and default value 
 - procedure XXX.Set to modify the value of a given option
 - procedure XXX.Accept to parse and store a option value passed as string
 - procedure XXX.Write to write the value of a given option
 - function XXX.Copy to create a duplicate of the option and its value
*)

PROCEDURE (opt: BooleanOption) Set* (value: BOOLEAN);
  BEGIN
    opt. true := value;
    done := TRUE
  END Set;

PROCEDURE CreateBoolean* (name: ARRAY OF CHAR; default: BOOLEAN): BooleanOption;
  VAR
    bopt: BooleanOption;
  BEGIN
    NEW (bopt);
    InitOption (bopt, name);
    bopt. Set (default);
    RETURN bopt
  END CreateBoolean;

PROCEDURE (opt: BooleanOption) Accept* (str: ARRAY OF CHAR): BOOLEAN;
  BEGIN
    done := (str = "TRUE") OR (str = "FALSE");
    IF done THEN
      opt. Set (str = "TRUE")
    ELSE 
      error := "Boolean value (TRUE or FALSE) expected"
    END;
    RETURN done
  END Accept;
  
PROCEDURE (opt: BooleanOption) Write*;
  BEGIN
    IF opt. true THEN
      Out.String ("TRUE")
    ELSE
      Out.String ("FALSE")
    END
  END Write;

PROCEDURE (opt: BooleanOption) Copy* (): Option;
  VAR
    bopt: BooleanOption;
  BEGIN
    NEW (bopt);
    bopt^ := opt^;
    RETURN bopt
  END Copy;

PROCEDURE (opt: BooleanOption) CopyValue* (dest: Option);
  BEGIN
    dest(BooleanOption). true := opt. true
  END CopyValue;


PROCEDURE (opt: IntegerOption) Set* (value: LONGINT);
  VAR
    num: ARRAY 32 OF CHAR;
  BEGIN
    IF (value < opt. lower) OR (value > opt. upper) THEN
      error := "Integer value must be in the range ";
      IntStr.IntToStr (opt. lower, num);
      Strings.Append (num, error);
      Strings.Append (" <= x <= ", error);
      IntStr.IntToStr (opt. upper, num);
      Strings.Append (num, error);
      done := FALSE
    ELSE
      opt. value := value;
      done := TRUE
    END
  END Set;

PROCEDURE CreateInteger* (name: ARRAY OF CHAR; default: LONGINT; lower, upper: LONGINT): IntegerOption;
(* Create integer option `name' with `value'.  `lower' and `upper' set the
   valid bounds for it's value (it must be in the range 
   `lower<=x<=upper'). *)
  VAR
    iopt: IntegerOption;
  BEGIN
    NEW (iopt);
    InitOption (iopt, name);
    iopt. lower := lower;
    iopt. upper := upper;
    iopt. Set (default);
    RETURN iopt
  END CreateInteger;

PROCEDURE (opt: IntegerOption) Accept* (str: ARRAY OF CHAR): BOOLEAN;
  VAR
    int: LONGINT;
    format: SHORTINT;
  BEGIN
    IntStr.StrToInt (str, int, format);
    done := (format = Conv.strAllRight);
    IF done THEN
      opt. Set (int)
    ELSE
      error := "Number expected"
    END;
    RETURN done
  END Accept;

PROCEDURE (opt: IntegerOption) Write*;
  BEGIN
    Out.LongInt (opt. value, 0)
  END Write;

PROCEDURE (opt: IntegerOption) Copy* (): Option;
  VAR
    iopt: IntegerOption;
  BEGIN
    NEW (iopt);
    iopt^ := opt^;
    RETURN iopt
  END Copy;

PROCEDURE (opt: IntegerOption) CopyValue* (dest: Option);
  BEGIN
    dest(IntegerOption). value := opt. value
  END CopyValue;


PROCEDURE (opt: StringOption) Set* (value: ARRAY OF CHAR);
  BEGIN
    NEW (opt. value, Strings.Length (value)+1);
    COPY (value, opt. value^);
    done := TRUE
  END Set;

PROCEDURE CreateString* (name: ARRAY OF CHAR; default: ARRAY OF CHAR): StringOption;
  VAR
    sopt: StringOption;
  BEGIN
    NEW (sopt);
    InitOption (sopt, name);
    sopt. Set (default);
    RETURN sopt
  END CreateString;

PROCEDURE (opt: StringOption) Accept* (str: ARRAY OF CHAR): BOOLEAN;
  BEGIN
    opt. Set (str);
    RETURN done
  END Accept;

PROCEDURE (opt: StringOption) Write*;
  VAR
    found: BOOLEAN;
    pos: INTEGER;
  BEGIN
    Strings.FindNext ('"', opt. value^, 0, found, pos);
    IF found THEN  
      (* found " in string, so we switch delimiter *)
      Out.Char ("'");
      Out.String (opt. value^);
      Out.Char ("'")
    ELSE
      Out.Char ('"');
      Out.String (opt. value^);
      Out.Char ('"')
    END
  END Write;

PROCEDURE (opt: StringOption) Copy* (): Option;
  VAR
    sopt: StringOption;
  BEGIN
    NEW (sopt);
    sopt^ := opt^;
    RETURN sopt
  END Copy;

PROCEDURE (opt: StringOption) CopyValue* (dest: Option);
  BEGIN
    dest(StringOption). value := opt. value
  END CopyValue;



PROCEDURE (s: OptionsSection) Parse* (includeEnd: BOOLEAN);
(* Parses an OPTIONS section.  The parameter `undef' of `Init' determines how
   unregisterd are treated.  *)
  CONST
    symEndOfStream = 0;
    symString = 1;
    symSemicolon = 2;
    symComma = 3;
    symBecomes = 4;
    symIdent = 5;
    symNumber = 6;
    symEnd = 7;
    symDefine = 8;
  VAR
    str, name: Param.LargeString;
    opt: Option;
    sym: SHORTINT;                         (* set by `GetSym' *)
    currSymPos: LONGINT;                   (* set by `GetSym' *)
  
  PROCEDURE GetSym;
    BEGIN
      Param.in. SkipWhitespace;
      currSymPos := Param.in. CurrPos();
      IF Param.in. eos THEN
        sym := symEndOfStream
      ELSE
        CASE Param.in. currChar OF
        | "'", '"': 
          sym := symString; 
          Param.in. ReadString (str)
        | ";":
          sym := symSemicolon;
          Param.in. NextChar
        | ",":
          sym := symComma;
          Param.in. NextChar
        | ":":
          sym := symBecomes;
          Param.in. Match (":=")
        ELSE
          IF Param.IsNum (Param.in. currChar) OR 
             (Param.in. currChar = "-") OR (Param.in. currChar = "+") THEN
            Param.in. ReadInteger (str);
            sym := symNumber
          ELSIF Param.IsAlpha (Param.in. currChar) THEN
            Param.in. ReadIdent (str);
            IF includeEnd & (str = "END") THEN
              sym := symEnd
            ELSIF (str = "DEFINE") THEN
              sym := symDefine
            ELSE 
              sym := symIdent
            END
          END
        END
      END
    END GetSym;
    
  PROCEDURE Match (expected: SHORTINT);
    VAR
      str: ARRAY 32 OF CHAR;
    BEGIN
      IF (sym # expected) THEN
        CASE expected OF
        | symBecomes: str := ":="
        | symEnd: str := "END"
        END;
        Strings.Append (" expected", str);
        Param.in. Error (currSymPos, str)
      END;
      IF (expected # symEnd) THEN
        GetSym
      END
    END Match;
  
  PROCEDURE Create (name: ARRAY OF CHAR; register: BOOLEAN): Option;
    VAR
      opt: Option;
    BEGIN
      CASE sym OF
      | symString: opt := CreateString (name, "")
      | symNumber: opt := CreateInteger (name, 0, MIN (LONGINT), MAX (LONGINT))
      | symIdent : opt := CreateBoolean (name, FALSE)
      ELSE  
        Param.in. Error (currSymPos, "Illegal value");
        opt := NIL
      END;
      IF register & (opt # NIL) THEN
        s. Add (opt)
      END;
      RETURN opt
    END Create;
  
  PROCEDURE Accept (opt: Option; str: ARRAY OF CHAR);
    BEGIN
      IF (opt # NIL) THEN
        IF (opt IS StringOption) & (sym # symString) THEN
          Param.in. Error (currSymPos, "String expected")
        ELSIF ~opt. Accept (str) THEN
          Param.in. Error (currSymPos, error)
        END
      END
    END Accept;
  
  PROCEDURE Assign (def: BOOLEAN);
    BEGIN
      IF (sym = symIdent) THEN
        opt := s. Find (str);
        name := str;
        IF (opt = NIL) & 
           ((s. undef = undefError) OR (s. undef = forceDefine) & ~def) THEN
          Param.in. Error (currSymPos, "Variable not defined")
        ELSIF (opt # NIL) & def THEN
          Param.in. Error (currSymPos, "Variable already defined")
        END;
        GetSym;
        Match (symBecomes);
        IF (opt = NIL) THEN
          opt := Create (name, def OR (s. undef = acceptUndef))
        END;
        Accept (opt, str);
        GetSym
      ELSE
        Param.in. Error (currSymPos, "Variable name expected");
        GetSym
      END
    END Assign;
  
  BEGIN
    GetSym;
    LOOP
      IF (sym = symIdent) THEN
        Assign (FALSE)
      ELSIF (sym = symDefine) THEN
        GetSym;
        Assign (TRUE)
      END;
      IF (sym = symEndOfStream) OR (sym = symEnd) THEN
        EXIT
      END;
      IF (sym # symSemicolon) THEN
        Param.in. Error (currSymPos, "; expected")
      ELSE
        GetSym
      END
    END;
    IF includeEnd THEN
      Match (symEnd)
    END
  END Parse;

PROCEDURE (s: OptionsSection) Write*;
(* Writes contents of section. *)
  VAR
    opt: Option;
  BEGIN
    opt := s. optionList;
    WHILE (opt # NIL) DO
      Out.String ("  ");
      Out.String (opt. name^);
      Out.String (" := ");
      opt. Write;
      Out.Ln;
      opt := opt. next
    END
  END Write;


PROCEDURE Init* (undef: SHORTINT);
(* Registers the OPTIONS section for configuration files.  `undef'
   determines how undefined option names found during parsing are handled.
   Possible values are `undefError', `forceDefine', `ignoreUndef', or
   `acceptUndef' (see the declarations of the constants for details).  *)
  BEGIN
    options. undef := undef;
    Param.AddSection ("OPTIONS", options)
  END Init;

BEGIN
  NEW (options);
  options. optionList := NIL
END ParamOptions.
