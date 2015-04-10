(*	$Id: StdPragmas.Mod,v 1.8 1999/07/30 21:12:16 acken Exp $	*)
MODULE StdPragmas;
(*  Definitions of the standard pragma variables of the OOC front-end.
    Copyright (C) 1998-1999  Michael van Acken

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
  Options := ParamOptions, Pragmas := ParamPragmas, Config;

VAR  (* pragmas; these variable should only be read out by the frontend! *)
  (* The following variables correspond to pragmas enabling / disabling run-
     time checks: TRUE generates code for the check, FALSE omits it.  Default
     values for these variables are defined in `Config.Mod'.  A back-end should
     produce a warning if a check is enabled that it can't serve, ie it should
     scan the variables for illegal values after the config file and the 
     command line have been parsed, and it should modify the procedure 
     `Config.NotifyPragmaAssign' to detect invalid assignments.  *)
  caseSelectCheck-: Options.BooleanOption;
  (* trap if a case selector doesn't match any label; if this value is FALSE, 
     then the corresponding trap instruction is marked with the flag 
     `Data.instrIsDisbaled'  *)
  indexCheck-: Options.BooleanOption;
  (* trap if an array index is out of range; toggles `D.instrIsDisabled' flag 
     of bound-index instructions *)
  rangeCheck-: Options.BooleanOption;
  (* trap if a set value is out of range; toggles `D.instrIsDisabled' flag 
     of bound-range instructions *)
  derefCheck-: Options.BooleanOption;
  (* trap if an invalid pointer is dereferenced; in practice `invalid' means
     usually `NIL'; most systems will catch such an error anyway (segmentation
     violation), so enabling this check means that the program exits 
     gracefully, giving some sort of error message and possibly an indication
     of the faulty instruction; effects the `Data.instrCheckNil' flag of 
     access-heap, update-heap, array-length, and type-tag instructions *)
  functResult-: Options.BooleanOption;
  (* trap if a function procedure is left without a return statement; toggles 
    `D.instrIsDisabled' flag of trap-return instructions *)
  typeGuard-: Options.BooleanOption;
  (* trap if a type guard fails or no branch of a WITH statement triggers; 
     toggles `D.instrIsDisabled' flag of type-guard and trap-with instructions *)
  intOverflowCheck-: Options.BooleanOption;
  (* trap if an integer operation or a conversion to integer overflows; toggles
     placement of `instrCheckOverflow' flag *)
  intDivCheck-: Options.BooleanOption;
  (* trap if an integer division has a right hand side of zero; toggles
     placement of `instrCheckDiv' flag *)
  realOverflowCheck-: Options.BooleanOption;
  (* trap if an real operation overflows; toggles placement of 
     `instrCheckOverflow' flag *)
  realDivCheck-: Options.BooleanOption;
  (* trap if a real division has a right hand side of zero; toggles
     placement of `instrCheckDiv' flag *)
  
  warnings-: Options.BooleanOption;
  (* if `warnings. true=TRUE', write out warnings; that is, don't ignore calls
     to `Error.ErrXXX' with negative error number *)
  assertions-: Options.BooleanOption;
  (* put assertions into output; toggles `D.instrIsDisabled' flag of 
     trap-assert instructions *)
  initialize-: Options.BooleanOption;
  (* initalize local variables and memory blocks to zero; toggles placement of
     `objIsInitialized' for variables (handled by the front-end), and 
     `instrInitialize' flags for the instructions `new' and `new-block' *)
  poisonHeap-: Options.IntegerOption;
  (* fill memory blocks with this byte value if >= 0; toggles placement of
     `instrPoisonHeap' flags for the instructions `new' and `new-block' *)
  stackCheck-: Options.BooleanOption;
  (* put code to check for stack overflow into procedure and module bodies; 
     toggles placement of `Data.instrStackCheck' flag in enter instructions *)
  conformantMode-: Options.BooleanOption;
  (* if TRUE, disable all language features of OOC that deviate from the 
     language report or common ETH usage; note that this doesn't disable the 
     scanner's pragma mechanism, basically because this mechanism doesn't work
     on the language level, but rather on a plain text *)
  (* note: pragma variable `warnings' is declared in `Error' *)

  (* COMPILER* and TARGET* pragma variables; their default values are taken
     from module `Config' *)
  compiler-: Options.StringOption;
  compilerVersion-: Options.StringOption;
  compilerMajor-: Options.IntegerOption;
  compilerMinor-: Options.IntegerOption;
  targetOS-: Options.StringOption;
  targetArch-: Options.StringOption;
  targetArchMinor-: Options.StringOption;
  targetInteger-: Options.IntegerOption;
  targetAddress-: Options.IntegerOption;
  targetByteOrder-: Options.StringOption;
  

PROCEDURE CreatePragma (VAR pragma: Options.BooleanOption; name: ARRAY OF CHAR;
                        default: BOOLEAN);
  BEGIN
    pragma := Options.CreateBoolean (name, default);
    Pragmas.pragmas. Add (pragma)
  END CreatePragma;

PROCEDURE Init*;
  BEGIN
    CreatePragma (warnings, "Warnings", Config.defaultWarnings);
    CreatePragma (assertions, "Assertions", Config.defaultAssertions);
    CreatePragma (initialize, "Initialize", Config.defaultInitialize);
    CreatePragma (stackCheck, "StackCheck", Config.defaultStackCheck);
    CreatePragma (conformantMode, "ConformantMode", Config.defaultConformantMode);

    CreatePragma (caseSelectCheck, "CaseSelectCheck", Config.defaultCaseSelectCheck);
    CreatePragma (indexCheck, "IndexCheck", Config.defaultIndexCheck);
    CreatePragma (rangeCheck, "RangeCheck", Config.defaultRangeCheck);
    CreatePragma (derefCheck, "DerefCheck", Config.defaultDerefCheck);
    CreatePragma (functResult, "FunctResult", Config.defaultFunctResult);
    CreatePragma (typeGuard, "TypeGuard", Config.defaultTypeGuard);
    CreatePragma (intOverflowCheck, "OverflowCheck", Config.defaultIOverflowCheck);
    CreatePragma (intDivCheck, "IntDivCheck", Config.defaultIDivCheck);
    CreatePragma (realOverflowCheck, "RealOverflowCheck", Config.defaultROverflowCheck);
    CreatePragma (realDivCheck, "RealDivCheck", Config.defaultRDivCheck);

    poisonHeap := Options.CreateInteger ("PoisonHeap", -1, -1, 255);
    Pragmas.pragmas. Add (poisonHeap);
    
    compiler := Options.CreateString ("COMPILER", Config.defaultCompiler);
    Pragmas.pragmas. Add (compiler);
    compilerVersion := Options.CreateString ("COMPILER_VERSION", Config.defaultCompilerVersion);
    Pragmas.pragmas. Add (compilerVersion);
    compilerMajor := Options.CreateInteger ("COMPILER_MAJOR", Config.defaultCompilerMajor, 0, 999);
    Pragmas.pragmas. Add (compilerMajor);
    compilerMinor := Options.CreateInteger ("COMPILER_MINOR", Config.defaultCompilerMinor, 0, 999);
    Pragmas.pragmas. Add (compilerMinor);
    targetOS := Options.CreateString ("TARGET_OS", Config.defaultTargetOS);
    Pragmas.pragmas. Add (targetOS);
    targetArch := Options.CreateString ("TARGET_ARCH", Config.defaultTargetArch);
    Pragmas.pragmas. Add (targetArch);
    targetArchMinor := Options.CreateString ("TARGET_ARCH_MINOR", Config.defaultTargetArchMinor);
    Pragmas.pragmas. Add (targetArchMinor);
    targetInteger := Options.CreateInteger ("TARGET_INTEGER", Config.defaultTargetInteger, 1, 256);
    Pragmas.pragmas. Add (targetInteger);
    targetAddress := Options.CreateInteger ("TARGET_ADDRESS", Config.defaultTargetAddress, 1, 256);
    Pragmas.pragmas. Add (targetAddress);
    targetByteOrder := Options.CreateString ("TARGET_BYTE_ORDER", Config.defaultTargetByteOrder);
    Pragmas.pragmas. Add (targetByteOrder)
  END Init;

END StdPragmas.
