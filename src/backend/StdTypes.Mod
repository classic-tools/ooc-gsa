(* 	$Id: StdTypes.Mod,v 1.28 1999/06/03 12:11:40 acken Exp $	 *)
MODULE StdTypes;
(*  Configures size and value range of predefined types.
    Copyright (C) 1995-1999  Michael van Acken

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
  D := Data, Opc := Opcode, Pragmas := ParamPragmas, ParamOptions, Error;


CONST
  (* MIN/MAX values of the standard data types; these should be the same for 
     all target architectures! *)
  minChar8*    = 0;             maxChar8*    = 0FFH;   (* mapped to integer *)
  minChar16*   = 0;             maxChar16*   = 0FFFFH; (* mapped to integer *)
  minShortInt* = -80H;          maxShortInt* = 07FH;
  minInteger*  = -8000H;        maxInteger*  = 07FFFH;
  minLongInt*  = -7FFFFFFFH-1;  maxLongInt*  = 07FFFFFFFH;
  minHugeInt*  = minLongInt;    maxHugeInt*  = maxLongInt;
  minReal*     = -3.40282347E+38;
  maxReal*     = 3.40282347E+38;
  minLongReal* = -1.7976931348623157D+308;
  maxLongReal* = 1.7976931348623157D+308;
  minSet8*     = 0;             maxSet8*     = 7;
  minSet16*    = 0;             maxSet16*    = 15;
  minSet32*    = 0;             maxSet32*    = 31;
  minSet64*    = 0;             maxSet64*    = 63;


CONST
  (* ansi-c specific: additional values for `Data.Object.beFlags'; the flag ids
     relative to zero are written into the symbol file by adjusting the
     constant `objExportMaskBE' accordingly *)
  objFixedName* = 0;       (* link name is given by user *)
  objCodeFile* = 1;        (* module also generates code *)
  objInterfaceModule* = 2; (* INTERFACE module *)
  objForeignModule* = 3;   (* FOREIGN module *)
  objInitFct* = 4;         (* module has function M_init *)
  objInLibrary* = 5;       (* module code is part of a library file *)
  objLibraryMaster* = 6;   (* set for main module of a library *)
  objExportMaskBE* = {objFixedName..objLibraryMaster};

  objEmitted* = 31;
  objInProgress* = 30;
  objIncluded* = 29;       (* include statement for module emitted *)
  objNeedPrototype* = 28;  (* put prototype of fct into .d *)
  objLocalCopy* = 27;      (* value parameter copied to local var *)
  objNoLocalCopy* = 26;    (* NO_COPY flag for value parameters *)
  objUsedLocalVar* = 25;   (* local var is used in C code *)

CONST
  (* ansi-c specific: additional values for `Data.Struct.beFlags'; the flag ids
     starting at zero are written into the symbol file by adjusting the
     `structExportMaskBE' constant accordingly *)
  structSpecialCallConv* = 0;
  (*...structAttribStdCall* = 1;  unused *)
  structAlign1* = 2;       (* maximum alignment is 1 *)
  structAlign2* = 3;       (* maximum alignment is 2 *)
  structAlign4* = 4;       (* maximum alignment is 4 *)
  structAlign8* = 5;       (* maximum alignment is 8 *)
  structExportMaskBE* = {structSpecialCallConv..structAlign8};
  
  structEmitted* = 31;
  structInProgress* = 30;
  structTDEmitted* = 29;
  structNamed* = 28;
  

PROCEDURE IntType* (value: LONGINT): D.Struct;
(* Get the integer constant's type based on its value.  Result is the smallest
   integer type that can hold `value'.  *)
  BEGIN
    IF (minShortInt <= value) & (value <= maxShortInt) THEN
      RETURN D.struct[D.strShortInt]
    ELSIF (minInteger <= value) & (value <= maxInteger) THEN
      RETURN D.struct[D.strInteger]
    ELSIF (minLongInt <= value) & (value <= maxLongInt) THEN
      RETURN D.struct[D.strLongInt]
    ELSE
      RETURN D.struct[D.strHugeInt]
    END
  END IntType;

PROCEDURE CharType* (value: LONGINT): D.Struct;
(* Get the character constant's type based on its value.  Result is the 
   smallest character type that can hold `value'.  *)
  BEGIN
    IF (value <= maxChar8) THEN
      RETURN D.struct[D.strChar8]
    ELSE
      RETURN D.struct[D.strChar16]
    END
  END CharType;

PROCEDURE ValidChar* (value: LONGINT): BOOLEAN;
(* Returns TRUE iff `value' is in the range MIN(LONGCHAR)..MAX(LONGCHAR).  *)
  BEGIN
    RETURN (minChar16 <= value) & (value <= maxChar16)
  END ValidChar;

PROCEDURE ValidReal* (value: LONGREAL): BOOLEAN;
(* Returns TRUE iff `value' is mapped onto the range MIN(REAL)..MAX(REAL) if
   it would be converted to a REAL value.  Rounding to nearest/evan is assumed.
   Note for maintainer: If you change this you need to change to corresponding
   macro in __oo2c.h, too.  *)
  CONST
    eps = 1.0141204801825835D+31;
    (* equals 2^103, half of the difference between two consecutive IEEE single
       precision floating point numbers with maximum exponent *)
  BEGIN
    RETURN (minReal-eps < value) & (value < maxReal+eps)
  END ValidReal;

PROCEDURE ValidInt* (value: LONGREAL): BOOLEAN;
(* Returns TRUE iff `ENTIER(value)' would be a valid LONGINT value.
   Note for maintainer: If you change this you need to change to corresponding
   macro in __oo2c.h, too.  *)
  BEGIN
    RETURN (MIN (LONGINT) <= value) & (value-1 < MAX(LONGINT))
  END ValidInt;


PROCEDURE Max* (form: SHORTINT): D.Const;
(* Returns the constant value of MAX(`form').  *)
  VAR
    int: LONGINT;
    real: LONGREAL;
  BEGIN
    IF (form IN {D.strReal, D.strLongReal}) THEN
      CASE form OF
      | D.strReal:     real := maxReal
      | D.strLongReal: real := maxLongReal
      END;
      RETURN D.GetRealConst (real, D.struct[form])
    ELSIF (form = D.strChar8) THEN
      RETURN D.GetIntConst (maxChar8, D.struct[D.strChar8])
    ELSIF (form = D.strChar16) THEN
      RETURN D.GetIntConst (maxChar16, D.struct[D.strChar16])
    ELSE
      CASE form OF
      | D.strShortInt: int := maxShortInt
      | D.strInteger:  int := maxInteger
      | D.strLongInt:  int := maxLongInt
      | D.strHugeInt:  int := maxHugeInt
      | D.strSet8:     int := maxSet8
      | D.strSet16:    int := maxSet16
      | D.strSet32:    int := maxSet32
      | D.strSet64:    int := maxSet64
      END;
      RETURN D.GetIntConst (int, IntType (int))
    END
  END Max;

PROCEDURE Min* (form: SHORTINT): D.Const;
(* Returns the constant value of MIN(`form').  *)
  VAR
    int: LONGINT;
    real: LONGREAL;
  BEGIN
    IF (form IN {D.strReal, D.strLongReal}) THEN
      CASE form OF
      | D.strReal:     real := minReal
      | D.strLongReal: real := minLongReal
      END;
      RETURN D.GetRealConst (real, D.struct[form])
    ELSIF (form = D.strChar8) THEN
      RETURN D.GetIntConst (minChar8, D.struct[D.strChar8])
    ELSIF (form = D.strChar16) THEN
      RETURN D.GetIntConst (minChar16, D.struct[D.strChar16])
    ELSE
      CASE form OF
      | D.strShortInt: int := minShortInt
      | D.strInteger:  int := minInteger
      | D.strLongInt:  int := minLongInt
      | D.strHugeInt:  int := minHugeInt
      | D.strSet8:     int := minSet8
      | D.strSet16:    int := minSet16
      | D.strSet32:    int := minSet32
      | D.strSet64:    int := minSet64
      END;
      RETURN D.GetIntConst (int, IntType (int))
    END
  END Min;


PROCEDURE PassPerReference* (obj: D.Object; considerVarPar: BOOLEAN): BOOLEAN;
(* This predicate decides if the variable `obj' is passed per reference (i.e. 
   the caller gets a pointer to its value), or per value (i.e. the caller gets
   a copy of the argument's value).  If `considerVarPar=TRUE', then result has 
   to be TRUE if `obj.mode = D.objVarPar', otherwise the decision should be 
   based solely on the type of the object `obj.type'.  Usually `obj' is a 
   formal parameter, although the ANSI-C back-end calls this procedure for
   arbitrary variables.  *)
  VAR
    form: SHORTINT;
  BEGIN
    IF considerVarPar & (obj. mode = D.objVarPar) THEN
      (* variable parameter's are always passed per reference *)
      RETURN TRUE
    ELSIF (obj. mode = D.objVar) THEN
      (* structured types are passed per reference; while not exactly necessary
         for record types, it's probably required for open array types; and: 
         delaying the creation of the value parameter's copy has the advantage 
         that the called procedure can decide to skip the copy and use the 
         original pointer instead (such a decision is quite complicated and 
         one needs a thorough dependence analysis in the general case; a simple
         example where a copy can be avoided is Strings.Length) *)
      form := obj. type. form;
      RETURN (form = D.strArray) OR (form = D.strOpenArray) OR 
             (form = D.strRecord) OR 
             (form = D.strComplex) OR (form = D.strLongComplex)
    ELSE
      RETURN FALSE
    END
  END PassPerReference;

PROCEDURE StructAlloc* (t: D.Struct);
(* The procedure `StructAlloc' maps a type `t' onto the destination 
   architecture, i.e. sets size and aligment of `t', and offsets of record 
   fields (the index of a type-bound procedure in the type descriptor is set 
   by the front-end).  This function has to be provided by the back-end.  
   Additional value for `t.size':
     `t.size=-2': not computable size (like for open arrays)
   If the back-end wants to emit errors or warnings, e.g. for huge types, it 
   has to check that `t. pos' isn't negative and pass it to one of the 
   `Error.ErrXXX' procedures together with a suitable error code.  `t. pos' is
   negative if `t' is an imported type; no warning should be emitted for this 
   case.  The implementation of `StructAlloc' can assume that it has already 
   been called on `t's base type(s) (except for pointer base types).
   Note: Compilation errors may create illegal types of `t.form=strUndef' 
   (their size and alignment is 1), but `t' is never NIL.  *)
  VAR
    obj: D.Object;
    size: LONGINT;
    align, i, maxAlign, fieldAlign: INTEGER;
  BEGIN
    t. align := -1;
    CASE t. form OF
    | D.strBoolean, D.strChar8, D.strShortInt, D.strSet8, D.strByte:
      t. size := 1
    | D.strInteger, D.strChar16, D.strSet16:
      t. size := 2
    | D.strLongInt, D.strReal, D.strSet32:
      t. size := 4
    | D.strHugeInt, D.strLongReal, D.strSet64:
      t. size := 8
    | D.strPtr, D.strPointer, D.strProc:
      IF (D.strAddress = D.strLongInt) THEN
        t. size := 4
      ELSE
        t. size := 8
      END
    | D.strOpenArray:
      t. size := -2;                     (* uncomputable size *)
      t. align := t. base. align
    | D.strArray:
      t. size := t. len * t. base. size;
      t. align := t. base. align
    | D.strRecord:
      (* initialize size and alignment, take base type into account *)
      IF (t. base = NIL) THEN 
        align := 1;  (* this alignment is also used if the record is empty *)
        size := 0
      ELSE
        align := t. base. align;
        size := t. base. size
      END;
      
      (* determine maximum alignment value, as selected by ALIGN[1248] *)
      IF (t. beFlags*{structAlign1..structAlign8} # {}) THEN
        i := structAlign8;
        WHILE ~(i IN t. beFlags) DO
          DEC (i)
        END;
        maxAlign := SHORT (ASH (1, i-structAlign1))
      ELSE
        maxAlign := MAX (INTEGER)
      END;
      
      (* assign offsets to record fields, take alignment into account *)
      obj := t. decl;
      WHILE (obj # NIL) DO
        IF (obj. mode = D.objField) THEN
          fieldAlign := obj. type. align;
          IF (fieldAlign > maxAlign) THEN
            fieldAlign := maxAlign
          END;
          
          IF (fieldAlign > align) THEN
            (* record's alignment is the highest alignment of all fields *)
            align := fieldAlign
          END;
          
          IF (D.structUnion IN t. flags) THEN
            (* union type: map all fields to the same offset 0; the overall 
               size is equal to the size of the largest union element *)
            obj. offset := 0;
            IF (obj. type. size > size) THEN
              size := obj. type. size
            END
          ELSE
            (* record type: adjust the offset to satisfy the field's alignment
               requirements, then add field size to record size *)
            IF (size MOD fieldAlign # 0) THEN
              INC (size, fieldAlign - size MOD fieldAlign)
            END;
            obj. offset := size;
            INC (size, obj. type. size)
          END
        END;
        obj := obj. rightObj
      END;
      
      (* adjust record size to be a multiple of its alignment *)
      IF (size MOD align # 0) THEN
        t. size := size + align - size MOD align
      ELSE
        t. size := size
      END;
      t. align := align
    END;
    IF (t. align < 0) THEN
      (* if not specified otherwise set aligment to size *)
      t. align := SHORT (t. size)
    END;
    
    IF (t. form = D.strProc) THEN
      (* mark all formal value parameter that are passed per reference *)
      obj := t. decl;
      WHILE (obj # NIL) DO
        IF (obj. mode = D.objVar) & PassPerReference (obj, FALSE) &
           ~(objNoLocalCopy IN obj. beFlags) THEN
          (* parameter must be copied into a local variable; or, to be precise,
             the parameter has to behave just like if it is been held in a 
             local variable *)
          INCL (obj. beFlags, objLocalCopy)
        END;
        obj := obj. rightObj
      END
    END
  END StructAlloc;


PROCEDURE WholeMax* (range: SHORTINT): LONGINT;
(* Returns the maximum value of a variable of type `range'.  The upper limit
   of "long unsigned" cannot be represented in a LONGINT value and is taken to
   be the maximum value of "long signed".  *)
  BEGIN
    CASE range OF
    | Opc.subclS: RETURN maxShortInt
    | Opc.subclSU: RETURN maxShortInt-minShortInt
    | Opc.subclI: RETURN maxInteger
    | Opc.subclIU: RETURN maxInteger-minInteger
    | Opc.subclL, Opc.subclLU,
      Opc.subclLL, Opc.subclLLU: RETURN maxLongInt
    END
  END WholeMax;

PROCEDURE WholeMin* (range: SHORTINT): LONGINT;
(* Returns the minimum value of a variable of type `range'.  *)
  BEGIN
    CASE range OF
    | Opc.subclS: RETURN minShortInt
    | Opc.subclSU: RETURN 0
    | Opc.subclI: RETURN minInteger
    | Opc.subclIU: RETURN 0
    | Opc.subclL: RETURN minLongInt
    | Opc.subclLU: RETURN 0
    | Opc.subclLL: RETURN minHugeInt
    | Opc.subclLLU: RETURN 0
    END
  END WholeMin;


PROCEDURE NotifyPragmaAssign* (pragma: Pragmas.Pragma; pos: LONGINT);
(* Called whenever a pragma assignment or a define is executed by the scanner.
   `pos' is the position of the variable name, `pragma' the variable that has 
   been modified.  Invalid pragma settings, like enabling an unsupported
   runtime check, should cause a warning.
   Note: The driver oo2c checks that the variables aren't changed undetected by
         command line arguments, this procedures makes sure that pragmas 
         embedded in the source code are detected.  *)
  BEGIN
    IF ((pragma. name^ = "OverflowCheck") OR
        (pragma. name^ = "RealOverflowCheck")) &
       pragma(ParamOptions.BooleanOption). true THEN
      Error.ErrIns (pos, -601, pragma. name^);(* runtime check not supported *)
      pragma(ParamOptions.BooleanOption). Set (FALSE)
    END
  END NotifyPragmaAssign;



(* All previous declarations are used by the front-end.  The following
   procedure is only relevant for the ANSI-C back-end: *)

PROCEDURE BasicTypes* (form: SHORTINT; VAR name: ARRAY OF CHAR);
(* Maps the Oberon-2 basic types onto their C counterparts.  The type sizes 
   have to correspond to the ones given in `StructAlloc' above.  Changes to the
   type mapping can make changes to procedures in GenConst and to typdefs in
   lib/_StdTypes.h necessary.  *)
  VAR
    str: ARRAY 24 OF CHAR;
  BEGIN
    CASE form OF  (* assuming 32 bit target with 32 bits for addresses *)
    | D.strBoolean : str := "unsigned char"
    | D.strChar8:    str := "unsigned char"
    | D.strChar16:   str := "unsigned short int"
    | D.strShortInt: str := "signed char"
    | D.strInteger:  str := "short int"
    | D.strLongInt:  str := "int"
    | D.strHugeInt:  str := "hugeint"
    | D.strReal:     str := "float"
      (* adjust GenConst.Real if you change this *)
    | D.strLongReal: str := "double"
      (* adjust GenConst.Real if you change this *)
    | D.strSet8:     str := "unsigned char"
    | D.strSet16:    str := "unsigned short int"
    | D.strSet32:    str := "unsigned int"
    | D.strSet64:    str := "unsigned hugeint"
    | D.strByte:     str := "unsigned char"
    | D.strPtr:      str := "void*"
    | D.strNone:     str := "void"
    ELSE
      str := "_undef_"  (* should never be used *)
    END;
    COPY (str, name)
  END BasicTypes;

BEGIN
  D.setMask[D.strSet8-D.strSet8] := {minSet8..maxSet8};
  D.setMask[D.strSet16-D.strSet8] := {minSet16..maxSet16};
  D.setMask[D.strSet32-D.strSet8] := {minSet32..maxSet32};
  D.setMask[D.strSet64-D.strSet8] := {minSet32..maxSet32} (* not implemented *)
END StdTypes.
