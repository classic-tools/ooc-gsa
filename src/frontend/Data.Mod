(* 	$Id: Data.Mod,v 1.101 1999/11/06 12:06:36 ooc-devel Exp $	 *)
MODULE Data;
(*  Basic data definitions for the symbol table and GSA code.
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
  SYSTEM, Strings, Parameter, Opc := Opcode;


CONST
  undefPos* = -1;                        (* undefined file position *)

TYPE
  String* = Parameter.String;
  
  
TYPE
  Info* = POINTER TO InfoDesc;
  Node* = POINTER TO NodeDesc;
  Usable* = POINTER TO UsableDesc;
  Opnd* = POINTER TO OpndDesc;
  Const* = POINTER TO ConstDesc;
  Result* = POINTER TO ResultDesc;
  Addressable* = POINTER TO AddressableDesc;
  Object* = POINTER TO ObjectDesc;
  Struct* = POINTER TO StructDesc;
  Instruction* = POINTER TO InstructionDesc;
  Region* = POINTER TO RegionDesc;
  Gate* = POINTER TO GateDesc;
  Guard* = POINTER TO GuardDesc;
  Merge* = POINTER TO MergeDesc;
  GlobalRegion* = POINTER TO GlobalRegionDesc;  (* greg *)
  
  InfoDesc* = RECORD 
  END;
  
  NodeDesc = RECORD 
    (InfoDesc)
  END;
  
  UsableDesc* = RECORD 
    (NodeDesc)
    useList-: Opnd;
    (* list of uses (use-chain) of this given value (which may be a result, a 
       constant, or a variable); the uses are linked with `Opnd.nextUse' *)
    info*: Info;
    marker*: LONGINT;
    (* general purpose fields, can be used by optimization algorithms to store
       arbitrary attributes; make sure to initialize the field properly when
       you decide to use it: you can't make any assumptions on the value it
       may contain *)
  END;

  
  
TYPE
  Location* = POINTER TO LocationDesc;
  LocationDesc* = RECORD 
    (InfoDesc)
    (* location attribute for operands and results; back-end dependent 
       values *)
  END;

TYPE
  (* symbolic location attribute, set by the front-end for operands of an exit
     or call instruction, and for results of an enter or call instruction; 
     also used to denote the target/source of local variables for instructions
     that write to/read from $mem; in this case the location signals that an
     operand must be forced into memory or taken from memory;
     for debugging purposes only, the location attribute can also be the 
     `location'  field of an instruction or result, denoting the variable to 
     which its value is assigned (see option --gsa-assign in module WriteGSA)*)
  SymLocation* = POINTER TO SymLocationDesc;
  SymLocationDesc* = RECORD
    (LocationDesc)
    var-: Addressable;
    (* variable or structure whose value is described by the operand argument
       (or the instruction result) to which the instance of `SymLocation' 
       belongs  *)
    attrib-: INTEGER;
    (* defines if the location is the value of `var' (`attrib=symLocObject') or
       rather one of its attributes (see below) *)
  END;
  
CONST  (* see `SymLocation.attrib' *)
  symLocObject* = -3;
  (* value is the content of the object denoted by `var' *)
  symLocAddress* = -2;
  (* value is address of parameter in `var' *)
  symLocTypeTag* = -1;
  (* value is type tag of variable record parameter in `var' *)
  symLocLength0* = 0;                    (* all attribs >= 0 *)
  (* value is the length of dimension `attrib' of the open array parameter
     in `var' *)
     
TYPE
  OpndDesc = RECORD 
    (NodeDesc)
    arg-: Usable;
    (* reference to place that defines this operand's value; can be a result,
       a constant, or a variable *)
    nextUse-: Opnd;
    (* links that make up the uses list of a given value (which may be a 
       result, a constant, or a variable); the head of the list is 
       `Usable.useList' *)
    nextOpnd-: Opnd;
    (* links that make up the list of operands of an instruction; the head of
       the list is stored in `Instruction.opndList' *)
    instr-: Instruction;
    (* the instruction to which this operand belongs *)
    location*: Location;
    (* location attribute of operand, eg memory, register, stack, etc.; 
       back-end dependent *)
    pos*: LONGINT;
    (* file position that corresponds to this operand, at least for actual 
       procedure parameters and expression operands *)
  END;



TYPE
  ConstDesc* = RECORD 
    (UsableDesc)
    nextConst: Const;
    (* this link is used to manage a list of all defined constant values; the 
       head is the variable `constList' *)
    type*: Struct;  
    (* type associated with constant, the following fields are filled depending
       on `type. form' *)
    string*: String;
    (* String constant of arbitrary size; its length (excluding the
       terminating 0X) is stored in the field `int'. NOTE: this field holds
       both CHAR and LONGCHAR arrays.  The latter are encoded in two bytes,
       placing the most significant byte first.  DO NOT apply any of the 
       standard string operations on this field, because an encoded LONGCHAR 
       string can contain CHAR(0X) anywhere within the resulting CHAR sequence.
       You can get the length (i.e., the number of LONGCHAR characters) of a 
       LONGCHAR string from the field `int'.  *) 
    int*: LONGINT;
    (* holds a SHORTINT, INTEGER, LONGINT, CHAR, or BOOLEAN value; for a string
       constant (char8 or char16) it holds the number of characters in the
       string, disregarding the termination character 0X *)
    int2*: LONGINT;
    set*: SET;
    real*: LONGREAL;
    (* this field holds REAL and LONGREAL constants; these two are 
       distinguished by the field `type' *)
    preserve*: BOOLEAN
    (* if TRUE, then this constant object cannot be deallocated by FreeConst *)
  END;
 


TYPE
  ResultDesc = RECORD 
    (UsableDesc)
    nextResult-: Result;
    (* list of result for instructions that have more than one; for `result =
       resilt. instr' the result is already the intruction (i.e., the 
       instruction is the head of the result list) *)
    instr-: Instruction;
    (* the instruction to which this result belongs *)
    location*: Location;
    (* location attribute of result; for the results of a enter intruction 
       this will be set by the front-end to symbolic references to the
       parameters, otherwise it's NIL; the back-end puts its own locations 
       here, eg memory, register, stack, etc.  *)
    type-: Struct;
    (* type of value that is represented by this result; only set for results 
       that represent values on the language level, ie that are created as 
       part of an Oberon-2 designator or an expression, or if it is an address
       calculation (all addresses are mappend to LONGINT); it's NIL for 
       statements or if the result is a pseudo-variable *)
  END;

  
  
TYPE
  AddressableDesc = RECORD 
    (UsableDesc)
    currValue*: Usable;
    (* holds a variable's or structure's current value when building SSA form;
       initialized to hold the addressable itself, later set to its current
       value during parsing *)
    beInfo*: Info;
    (* place to put back-end specific information into symbol table, ie to add
       additional information to Struct and Object entities; initialized to NIL
       by the front-end; see also the flags objExportsBEInfo and 
       structExportsBEInfo defined below *)
  END;



TYPE
  ObjectDesc* = RECORD 
    (AddressableDesc)
    name*: String;  
    (* name of object *)
    type*: Struct;  
    (* the object's type *)
    mode*: SHORTINT;  
    (* identifies the kind of object, eg, constant, type, variable, etc.; for
       a complete list check the `objXXX' constants below *)
    leftObj*, rightObj*: Object;  
    (* links to sons in scope tree, the root is stored in `Object.localDecl'
       (for modules and procedures);  record fields and type-bound procedures
       are stored in a list linked with `Object.rightObj' whose head is stored
       in `Struct.decl' *)
    localTo*: Addressable;  
    (* object in whose scope this object is declared; for fields and type-bound
       procedures this is the record (i.e., a `Struct') they belong to, for all
       other declarations this is their module or procedure (i.e., an 
       `Object') *)
    localDecl*: Object;
    (* for a module or a procedure this is the root of a binary tree containing
       the declarations in its visibility scope; nodes of the the tree are 
       linked by the fields `leftObj' and `rightObj' *)
    moduleId*: INTEGER;
    (* the id of the module that defines this object *)
    level*: INTEGER;  
    (* nesting level of the object; for a module and all names declared 
       globally this is Sym.globalLevel (=0), for all other declarations it's
       the number of enclosing procedures; example: the formal parameters and
       all local variables of a global procedure have a level of 1 *)
    data*: Usable;  
    (* this is a `Const' (i.e., the constant's value) for a constant 
       declaration or a module, an `Object' (the receiver) for type-bound 
       procedures; for a parameter variable it refers to the corresponding 
       formal parameter of the procedure type description;  may be used by 
       front or back-end to keep additional info for other kinds of objects *)
    greg*: GlobalRegion;
    (* for a procedure or a module this is a reference to its global region; 
       it's NIL until the procedure or module body has been parsed completely*)
    offset*: LONGINT;
    (* field offset for record field (objField), index of type-bound procedure
       (objTBProc, index starts at 0) *)
    flags*: SET;  
    (* various flags, see `objXXX' constants below; except for 
       `objExportsBEInfo' the back-end shouldn't modify this field *)
    beFlags*: SET;
    (* the back-end can put flags for its own use here; initialized to {} when
       the object is created; the back-end is expected to define possible 
       entries for this set in its `StdTypes' module, together with a set 
       constant `objExportMaskBE'; only the value `beFlags*objExportMaskBE' 
       will be written to the symbol file; the front-end will write this field
       to and restore it from the symbol file *)
    pos*: LONGINT;  
    (* file position of the object's declaration; use this value when referring
       to a declaration in an error or warning message *)
  END;

CONST
  (* these values identify the various declared objects (see `Object. mode');  
     note: the symbol table distinguishes between two kinds of variables 
       `objVarPar': variable parameters, and
       `objVar': normal variables or value parameters  *)
  objUndef* = 0; objConst* = 1; objType* = 2;   objVar* = 3;  objVarPar* = 4; 
  objField* = 5; objProc* = 6;  objTBProc* = 7; objModule* = 8; 
  objRestParam* = 9;  (* special formal parameter `...' (for external C) *)
  
  (* object modifiers and signals (values for `Object.flags')
     note: all flags marked with [back-end] have to be set by the back-end when
           implementing system flags; usually they are set by the procedure
           SystemFlags.ObjectModifiers *)
  objIsUsed* = 31;
  (* object is referenced at least once *)
  objIsForwardDecl* = 30;
  (* type or procedure was created as a result of a forward declaration and is
     not properly defined yet; this flags is cleared as soon as the header of 
     the actual procedure definition is parsed, or after the forward declared 
     type has been defined completely*)
  objWasForwardDecl* = 29;
  (* set if a the object has been a forward declaration, but was resolved in 
     the meantime; set at the same time as `objIsForwardDecl' is cleared *)
  objContainsProc* = 28;
  (* scope contains locally defined procedures *)
  objInSymbolFile* = 27;
  (* object is part of the written symbol file, but not nessesarily visible;
     the flag `objIsExported' doesn't have to be set together with this flag.
     for a module this flag means that a type from the module is part of the
     currently compiled module's symbol file *)
  objIsParameter* = 26;
  (* variable is part of a procedure's parameter list or is the receiver *)
  objIsReceiver* = 25;
  (* variable is the receiver of a type-bound procedure *)
  objIsUsedNonlocal* = 24;
  (* set for a variable or a procedure if it is accessed from a procedure that
     is nested into the scope that defines the object; note that this flag may 
     be set incorrectly if the nested procedure isn't called or if it is 
     inlined into the procedure that declares the object *)
  objHasBody* = 23;
  (* modifies parsing; if not set for a procedure object, then the parser 
     won't look for local declarations or a procedure body;  if not set for a
     module object, then the parser won't look for a module body; this flag is
     set by default, has to be cleared by the back-end for external modules *)
  objIsInitialized* = 22;
  (* this is set for a local variable if the variable is declared in a piece of
     code where `Initialize=TRUE' holds *)
  objIsTwisted* = 21;
  (* set if this object is a formal parameter whose type is currently twisted
     by a WITH statement *)
  objNotSideEffected* = 20;
  (* used by the front-end to indicate that the variable should not appear as
     operand of a collecting, nor as result of a reclaiming instruction *)
  objIsUpdated* = 19;
  (* set for a variable of a procedure (or module) scope `Foo' if the value of 
     the variable is changed during the execution of `Foo's body; this 
     information should be available by scanning the scope's greg, but it is
     current impossible to attain for local variables of structured under 
     certain circumstances; therefore this flag is set by the front-end,
     regardless of optimizations down the road that may remove the update
     in question
     NOTE: at the moment this flag is only set for parameters *)
  objAllowsSystemFlags* = 18;
  (* [back-end] if set for a module, then the user can add system flags to
     object and type declarations in the module's source code *)
  (* note: add flags that aren't written into the symbol file here *)
  
  objIsExported* = 0;
  (* object is exported, i.e. visible outside the current module;  the flag
     `objIsExportedReadOnly' toggles between read-only and read/write export *)
  objIsExportedReadOnly* = 1;
  (* variable or field is not writable outside this module *)
  objReadBeforeWrite* = 2;
  (* the formal variable parameter is (or may be) read before something is 
     assigned to it *)
  objExportsBEInfo* = 3;
  (* [back-end] object writes additional, back-end specific, information into
     the symbol file; a similar flag exists for Structs; see also the back-end
     module SystemFlags, procedures (Read|Write)(Object|Struct)Info *)
  objAllowsUnderscore* = 4;
  (* [back-end] set for a module object if names declared in it can contain an
     underscore in place of a letter *)
  objNoLengthTag* = 5;
  (* [back-end] set for a formal open array parameter if it isn't accompanied 
     by length tags for each of its open dimensions (e.g. C array parameters);
     LEN cannot be called on such a parameter and it cannot be passed to a 
     parameter that expects length tags *)
  objNoTypeTag* = 6;
  (* [back-end] set for a formal variable parameter of record type if it isn't
     accompanied by a type tag (e.g. C record parameter); for such a parameter 
     it's assumed that its static and its dynamic type are identic *)
  objNilCompat* = 7;
  (* [back-end] set for a formal parameter if the value NIL can be used for its
     argument; used to model C functions that accept an array parameter or NIL
     as argument *)
  objIsSpecialCodeProc* = 8;
  (* [back-end] set if the procedure represents a procedure whose code is 
     generated by the compiler, even if the procedure is declared in an 
     external module; used to implement direct calls of math functions built 
     into the processor, or procedures that can't be implemented in the usual 
     way (like the oo2c implementation of Exceptions.PUSHCONTEXT); the object's
     `data' field will refer to a constant whose `int' field holds the id of 
     the procedure; note that only normal procedures can be declared "special",
     and that it isn't possible to assign such a procedure to a variable *)
  objAbstractTBProc* = 9;
  (* [back-end] abstract type-bound procedures can only be declared for records
     that are likewise marked as abstract; an abstract tb proc has no body;
     a non-abstract record cannot inherit abstract tb procs *)
  objFinalTBProc* = 10;
  (* when set, this procedure cannot be redefined for any extension of the
     type-bound procedure's base type; a call to such a procedure does not
     need to look up the redirection table, it can use the procedure's address
     directly; this flag is set by the front-end after all declarations of a 
     module have been parsed *)
     
  (* note: add flags that are written into the symbol file here *)
  objExportMask* = {objIsExported..objFinalTBProc};
  (* only the value of `Object.flags * objExportMask' will be be written to 
     the symbol file, the rest is either discarded or reconstructed while
     reading the file *)
  


TYPE
  StructDesc = RECORD 
    (AddressableDesc)
    form*: SHORTINT;
    (* class of type, see `strXXX' constants below *)
    base*: Struct;
    (* contains pointer base type, array element type, record base type (NIL
       if the record isn't an extension), or a procedure result type *)
    decl*: Object;
    (* the formal parameter list for procedure types and for procedure 
       declarations, or, for record types, the list of fields and type-bound
       procedures; the parameters (fields, type-bound procedures) are linked 
       with `Object.rightObj' *)
    len*: LONGINT;
    (* for an array type this holds its length; for a record type this is the
       extension level of the record (0 means no base type) *)
    obj*: Object;
    (* this field is NIL for type constructs that are not associated with a
       name, otherwise it's the name (the object) that is initially assigned to
       this type (due to type aliases a type may be referenced by multiple 
       names) *)
    flags*: SET;
    (* various flags, see `structXXX' below; except for `structExportBEInfo' 
       the back-end shoudn't modify this field *)
    beFlags*: SET;
    (* the back-end can put flags for its own use here; initialized to {} when
       the structure is created; the back-end is expected to define possible 
       entries for this set in its `StdTypes' module, together with a set 
       constant `objExportMaskBE'; only the value `beFlags*structExportMaskBE' 
       will be written to the symbol file; the front-end will write this field
       to and restore it from the symbol file *)
    size*: LONGINT;
    (* type size, set by calling `StdTypes.StructAlloc' *)
    align*: INTEGER;
    (* type alignment, set by calling `StdTypes.StructAlloc' *)
    pos*: LONGINT;
    (* file position of the type constructor that defined this type; note: this
       is not equal to the position of a type declaration that provides a name
       for the type *)
  END;

CONST
  (* The following values define different types.  The first group (strUndef to
     strNone) defines atomic types, the second structured types.  The symbols
     `strNil' and `strStringConst' denote the special types of NIL and string
     constants, `strNone' the result type of a proper procedure.  *)
  strUndef* = 0;        strBoolean* = 1;
  strChar8* = 2;        strChar16* = 3;
  strShortInt* = 4;     strInteger* = 5;      strLongInt* = 6; strHugeInt* = 7;
  strReal* = 8;         strLongReal* = 9;
  strComplex* = 10;     strLongComplex* = 11;
  strSet8* = 12;        strSet16* = 13;       strSet32* = 14;  strSet64* = 15;
  strByte* = 16;        strPtr* = 17;
  strStringConst8* =18; strStringConst16* =19;
  strNil* = 20;         strNone* = 21;
  (* in the compiler sources addresses are assigned the virtual type 
     `strAddress'; this type is always an alias to an existing integer type;
     on 32bit systems it is equivalent to LONGINT *)
  strAddress* = strLongInt;
  (* markers for structured types;  arrays are separated into `normal', i.e.
     fixed length arrays, and open arrays *)
  strPointer* = 27; strProc* = 28; strArray* = 29; strOpenArray* = 30; 
  strRecord* = 31;

  (* groups of types used by predefined operators and procedures; the function
     `SymbolTable.TypeInGroup' tests membership of a type in one of this 
     groups *)
  grpInteger* = 32;                      (* SHORTINT, INTEGER, LONGINT *)
  grpReal* = 33;                         (* REAL, LONGREAL *)
  grpNumeric* = 34;                      (* SHORTINT .. LONGREAL *)
  grpComplex* = 35;                      (* COMPLEX, LONGCOMPLEX *)
  grpChar* = 36;                         (* CHAR, LONGCHAR *)
  grpSet* = 37;                          (* any set type (SET8-SET64) *)
  grpString8* = 38;                      (* ARRAY [n] OF CHAR, string8 *)
  grpString16* = 39;                     (* ARRAY [n] OF LONGCHAR, string16 *)
  grpStringConst* = 40;                  (* CHAR or LONGCHAR string const *)
  grpAnyString* = 41;                    (* any char array of string const *)
  grpArray* = 42;                        (* ARRAY [n] OF *)
  grpCharArray* = 43;                    (* ARRAY [n] OF (CHAR|LONGCHAR) *)
  grpPointer* = 44;                      (* all POINTER TO types *)
  grpProc* = 45;                         (* all PROCEDURE types *)
  grpPtr* = 46;                          (* all pointer types (incl PTR) *)
  grpStructured* = 47;                   (* ARRAY [n] OF, RECORD, complex *)
  grpLong* = 48;                         (* types applicable to LONG *)
  grpShort* = 49;                        (* types applicable to SHORT *)
  grpNilCompat* = 50;                    (* to NIL compatible types *)
  grpShift* = 51;                        (* types accepted by LSH, ROT *)
  grpGetPut* = 52;                       (* types accepted by GET, PUT, etc. *)
  grpAnyType* = 53;                      (* arbitrary type *)

  grpOffset* = -32;  (* used to map group ids to SET range *)
  
  (* flags that modify certain aspects of types (value for `Struct.flags')
     note: all flags marked with [back-end] have to be set by the back-end when
           implementing system flags; usually they are set by the procedure
           SystemFlags.StructModifiers *)
  structInSymbolFile* = 31;
  (* structure is part of the written symbol file, but not nessesarily 
     visible outside its module *)
  structEnableRestParam* = 30;
  (* [back-end] if set for a formal parameter type, then the special parameter
     `...' is allowed as last parameter *)
  structIsExported* = 29;
  (* if set, then this type has been named, and at least one of the names
     has been marked as exported *)
  (* note: add flags that aren't written into the symbol file here *)
  maxStructFlag* = 28;                   (* last free struct flag *)
  
  structExportsBEInfo* = 0;
  (* [back-end] structure writes additional, back-end specific, information 
     into the symbol file; a similar flag exists for Objects; see also the
     back-end module SystemFlags, procedures (Read|Write)(Object|Struct)Info *)
  structAllowsUnderscore* = 1;
  (* [back-end] set for a record type if its field and tb proc names it can 
     contain an underscore in place of a letter *)
  structNotExtensible* = 2;
  (* [back-end] set if the record cannot serve as another record's base type;
     used to model non-Oberon record types (like Modula-2 and C) *)
  structNoDescriptor* = 3;
  (* [back-end] set if the record or array type has no corresponding run-time
     type descriptor; this signals the front-end that instances of this type
     (arrays, records, or a derived pointer type) cannot appear as rhs of a 
     type test or type guard *)
  structNoLengthInfo* = 4;
  (* [back-end] set if variables of this open array type don't know how much
     elements they contain (like C arrays); LEN cannot be called on such a
     variable and it cannot be passed to a parameter that expects length 
     tags *)
  structStaticPointer* = 5;
  (* [back-end] set for a pointer type if variables of this type have no type
     tag and therefore no dynamic type differing from the static one; in type
     tests such variables have always their static type, unless the base 
     record is `structNoDescriptor', in which case type tests are illegal *)
  structDisableNew* = 6;
  (* [back-end] set for a pointer type if the predefined function NEW cannot
     allocate memory for it; should be set for pointers to open arrays without
     length info and to records without type tags, in order to highlight the
     fact that they aren't standard Oberon types *)
  structUnion* = 7;
  (* [back-end] set for a record type if its fields should be mapped like a C
     union type, i.e. all start at offset 0 *)
  structCArrayAssign* = 8;
  (* [back-end] set for a "pointer to array" type to enable C-like assignment 
     semantics; if the right side of the assignment is a compatible array 
     variable (or string), then the address of the array is assigned to the 
     pointer; note: the pointer's base array must have the flags 
     `structNoDescriptor' and `structNoLengthInfo' set *)
  structAbstractType* = 9;
  (* [back-end] if set, a record cannot be instanciated, and abstract 
     type-bound procedures can be defined for it *)
  
  (* note: add flags that are written into the symbol file here *)
  structExportMask* = {structExportsBEInfo..structAbstractType};
  (* only the value of `Struct.flags * structExportMask' will be be written to 
     the symbol file, the rest is either discarded or reconstructed while
     reading the file *)
  
VAR
  setMask*: ARRAY strSet64-strSet8+1 OF SET;
  (* when creating a set constant with GetSetConst, the constant's value is 
     first clipped against the mask corresponding to its type; e.g. a constant
     of type SET8 is and'ed with {StdTypes.minSet8..StdTypes.maxSet8}; see also
     procedure GetSetConst and module StdTypes*)
  
TYPE
  InstructionDesc = RECORD 
    (ResultDesc)
    opndList-: Opnd;
    (* instruction's operand list; the operands are linked with `Opnd.
       nextOpnd' *)
    region-: Region;
    (* the region that contains this instruction (or, in GSA terms, the
       control-condition under which it is executed) *)
    nextInstr-, prevInstr-: Instruction;
    (* links that make up the list of instructions of a given region; the head
       of the list is stored in `Region.instrList' *)
    opcode*: INTEGER;
    (* instruction opcode, the symbolic names are defined in module `Opcode' *)
    flags*: SET;
    (* flags to modify the semantics of the instruction; values are defined
       below *)
    pos*: LONGINT;
    (* source code position associated with instruction *)
  END;

CONST
  instrNotDead* = 0;
  (* execution of the instruction may (or will) raise an exception; this 
     prevents this instruction from being removed during dead code 
     elimination; if set for a greg's enter instruction, then all calls to
     the corresponding procedure must be treated as "not dead" *) 
  instrIsDisabled* = 1;
  (* set for bound-index, bound-range, trap, etc. instructions if these 
     run-time checks are disabled by the user; the instruction are inserted 
     into the code to have semantic information like index restrictions 
     available in the intermediate code for optimizations and additional error
     checks; instructions marked with this flag are only removed as dead code 
     if the elimination procedure is called with the parameter `removeDisabled'
     set to `TRUE', which is usually the last step in the optimization phase.*)
  instrCheckOverflow* = 2;
  (* set if overflow checking should be done for this instruction; can be set
     for real or integer operators, and type conversions to integer *)
  instrCheckNil* = 3;
  (* set for an access-heap, update-heap, array-length, or type-tag instruction
     if the pointer value should be checked for NIL; can also be present for 
     call instructions activating a procedure variable; in this case a 
     procedure value of NIL should be recognized and reported by the program *)
  instrCheckDiv* = 4;
  (* set for integer div/mod or real div instruction if a zero right hand side
     should be catched *)
  instrInitialize* = 5;
  (* set for a new or new-block instruction if `Initialize=TRUE' holds just 
     before the first parameter, inidicating that the memory block should be 
     cleared *)
  instrStackCheck* = 6;
  (* set for an enter instruction if the back-end has to make sure that 
     execution of the corresponding global region will detect any stack 
     overflows *)
  instrUniqueResult* = 7;
  (* set if every invocation of the given instruction delivers another result,
     regardless of its arguments; no code transformation may change the dynamic
     execution count of such an instruction; examples are NEW (delivers always
     a new heap object) and sleep (always waits for the given amount of time):
     neither of those instructions may be folded away during common 
     subexpression elimination, or moved out of a loop *)
  instrGuardFor* = 8;
  (* this flag is set for the compare instruction that is generated to test
     if a FOR loop has ended; used temporarily by the front-end, cleared 
     afterwards *)
  instrPoisonHeap* = 9;
  (* set for a new or new-block instruction if `PoisonHeap >= 0' holds just 
     before the first parameter, inidicating that the memory block should be 
     filled with the indicated byte value after allocation; the allocated
     block is initialized with `StdPragmas.poisonHeap.value MOD 256' *)
  
  minInstrFlag* = 10;                    (* first free instr flag *)


TYPE
  GateDesc = RECORD
    (InstructionDesc)
    var-: Object;
    (* variable whose value is controlled by this gate *)
    oldValue*: Usable;
    (* every gate describes how a variables definition reaches this place on 
       different paths; this field stores the variable's value that holds 
       before the paths are split *)
  END;
  RegionDesc = RECORD
    (InstructionDesc)
    instrList-: Instruction;
    (* set of instructions that make up the region; the instructions are 
       linked with `Instruction.nextInstr' and `Instruction.nextInstr'; nested
       region are also considered to be instructions and are therefore part of
       this list;  note: the order of instructions in the list is not 
       relevant *)
    instrTail-: Instruction;
    (* last element of list of intructions in `instrList' *)
    regionList-: Region;
    (* set of regions that are nested inside the given region; the regions are
       linked with `Region.nextRegion' *)
    nextRegion-: Region;
    (* links that make up the list of regions inside a given region; the head 
       of the list is stored in `Region.regionList' *)
    merge*: Merge;
    (* this is the merge node into which gates have to be placed whenever an
       assignment is executed in this region; NIL denotes the exit instruction;
       only the front-end can rely on the information stored here, use tb proc
       `Region.RegionMerge' at any later stage *)
    rangeL, rangeH: INTEGER;
    (* used by the `Dominates' predicates *)
  END;
  GuardDesc = RECORD
    (RegionDesc)
  END;
  MergeDesc = RECORD
    (RegionDesc)
  END;
  GlobalRegionDesc = RECORD  (* greg *)
    (GuardDesc)
    bodyOf*: Object;
    (* for the top most region, this field contains a reference to the object
       (procedure, type-bound procedure, or module) whose body this region
       (abbreviated "greg") represents *)
    enter*, exit*: Instruction;
    (* the global region's enter and exit instruction *)
  END;
  
CONST
  noSymbolTable* = MIN (INTEGER);
  (* value of `Object.moduleId' for a module that hasn't compiled and whose
     symbol file has not been read; such a module object can only be created
     during a `make'  *)

CONST
  sizeConstList = 128;
  
VAR
  struct*: ARRAY strNone+1 OF Struct;
  (* structures of predefined types, set by `SymbolTable.Init' *)
  constList: ARRAY sizeConstList OF Const;
  (* list of all defined constants; linked with `Const.nextConst' *)
  constNil-: Const;
  (* constant object that represents the value NIL; only used in the front-end,
     replaced by 0 before control passes to the back-end *)
  constUndef-: Const;
  (* constant that can be used as instruction operand to signal a missing or
     undefined value; `constNil' cannot be used for this since it is replaced
     by the value 0 in the GSA code *)
  constRange: Const;
  (* list of range constants used as case labels *)
  i: INTEGER;  


PROCEDURE InitNode (node: Node);
  BEGIN
  END InitNode;

PROCEDURE InitUsable (u: Usable);
  BEGIN
    InitNode (u);
    u. useList := NIL;
    u. info := NIL;
    u. marker := -1
  END InitUsable;

PROCEDURE InitOpnd (opnd: Opnd);
  BEGIN
    InitNode (opnd);
    opnd. arg := NIL;
    opnd. nextUse := NIL;
    opnd. nextOpnd := NIL;
    opnd. instr := NIL;
    opnd. location := NIL;
    opnd. pos := undefPos
  END InitOpnd;

PROCEDURE InitConst* (c: Const; type: Struct);
  BEGIN
    InitUsable (c);
    c. type := type;
    c. int := 0; 
    c. int2 := 0; 
    c. real := 0.0; 
    c. set := {}; 
    c. string := NIL;
    c. nextConst := NIL;
    c. preserve := FALSE
  END InitConst;

PROCEDURE InitResult (res: Result; type: Struct);
  BEGIN
    InitUsable (res);
    res. nextResult := NIL;
    res. instr := NIL;
    res. location := NIL;
    res. type := type;
  END InitResult;

PROCEDURE InitAddressable (a: Addressable);
  BEGIN
    InitUsable (a);
    a. currValue := a;
    a. beInfo := NIL
  END InitAddressable;

PROCEDURE InitObject* (obj: Object; name: ARRAY OF CHAR; mode: SHORTINT; pos: LONGINT);
  BEGIN
    InitAddressable (obj);
    obj. type := NIL; 
    NEW (obj. name, Strings.Length (name)+1);
    COPY (name, obj. name^);
    obj. mode := mode;
    obj. leftObj := NIL; 
    obj. rightObj := NIL; 
    obj. localTo := NIL;
    obj. localDecl := NIL;
    obj. moduleId := noSymbolTable;
    obj. level := MIN (INTEGER);
    obj. data := NIL;
    obj. greg := NIL;
    obj. offset := MIN (LONGINT);
    obj. flags := {objHasBody};
    obj. beFlags := {};
    obj. pos := pos
  END InitObject;

PROCEDURE InitStruct* (str: Struct; form: SHORTINT; pos: LONGINT);
  BEGIN
    InitAddressable (str);
    str. form := form; 
    str. base := NIL; 
    str. decl := NIL;
    str. len := 0;
    str. obj := NIL; 
    str. flags := {}; 
    str. beFlags := {}; 
    str. size := MIN (LONGINT); 
    str. align := 1;
    str. pos := pos
  END InitStruct;

PROCEDURE InitInstruction (instr: Instruction; type: Struct; pos: LONGINT);
  BEGIN
    InitResult (instr, type);
    instr. instr := instr; (* an instruction is a result that defines itself *)
    instr. opndList := NIL;
    instr. region := NIL;
    instr. nextInstr := NIL;
    instr. prevInstr := NIL;
    instr. opcode := -1;
    instr. flags := {};
    instr. pos := pos
  END InitInstruction;

PROCEDURE InitRegion* (region: Region; pos: LONGINT);
  BEGIN
    InitInstruction (region, NIL, pos);
    region. instrList := NIL;
    region. instrTail := NIL;
    region. regionList := NIL;
    region. nextRegion := NIL;
    region. merge := NIL;
    region. rangeL := 0;
    region. rangeH := -1
  END InitRegion;

PROCEDURE CreateSymLocation* (var: Addressable; attrib: INTEGER): SymLocation;
  VAR
    loc: SymLocation;
  BEGIN
    NEW (loc);
    loc. var := var;
    loc. attrib := attrib;
    RETURN loc
  END CreateSymLocation;




PROCEDURE InsertUse (arg: Usable; opnd: Opnd);
(* Sets `opnd. arg = arg' and adds `opnd' to the list of uses of `arg'.  To be
   precise, `opnd' will be made the first element of the use list.  *)
  BEGIN
    opnd. arg := arg;
    opnd. nextUse := arg. useList;
    arg. useList := opnd
  END InsertUse;

PROCEDURE DeleteUse (opnd: Opnd);
(* Removes `opnd' from the list of uses of `opnd. arg'.  *)
  VAR
    prev: Opnd;
  BEGIN
    IF (opnd. arg. useList = opnd) THEN
      opnd. arg. useList := opnd. nextUse
    ELSE
      prev := opnd. arg. useList;
      WHILE (prev. nextUse # opnd) DO
        prev := prev. nextUse
      END;
      prev. nextUse := opnd. nextUse
    END;
    opnd. nextUse := NIL;
    opnd. arg := NIL
  END DeleteUse;


PROCEDURE (opnd1: Opnd) SwapArguments* (opnd2: Opnd);
(* Swap the arguments of the given operands, i.e., 
   do "swap (opnd1. arg, opnd2. arg)".
   pre: Both operands must belong to the same global region. *)
  VAR
    arg1, arg2: Usable;
  BEGIN
    arg1 := opnd1. arg;
    arg2 := opnd2. arg;
    DeleteUse (opnd1);
    DeleteUse (opnd2);
    InsertUse (arg1, opnd2);
    InsertUse (arg2, opnd1)
  END SwapArguments;



PROCEDURE (instr: Instruction) Operand* (arg: Usable);
(* Adds `arg' to the end of `instr's operand list.
   pre: arg # NIL *)

  PROCEDURE Append (VAR opnd: Opnd);
    BEGIN
      IF (opnd = NIL) THEN
        NEW (opnd);
        InitOpnd (opnd);
        (* append `opnd' to list of operands of `instr' *)
        opnd. instr := instr;
        (* add `opnd' to list of uses of `arg' *)
        InsertUse (arg, opnd)
      ELSE
        Append (opnd. nextOpnd)
      END
    END Append;
  
  BEGIN
    Append (instr. opndList)
  END Operand;

PROCEDURE (instr: Instruction) UniqueOperand* (arg: Usable; loc: Location);
(* Adds `arg' to the end of `instr's operand list, but only if `instr#arg' and
   `instr' doesn't have an argument with the value `arg' already.  The new
   operands locations is set to `loc'.
   pre: arg # NIL *)

  PROCEDURE Append (VAR opnd: Opnd);
    BEGIN
      IF (opnd = NIL) THEN
        NEW (opnd);
        InitOpnd (opnd);
        (* append `opnd' to list of operands of `instr' *)
        opnd. instr := instr;
        opnd. location := loc;
        (* add `opnd' to list of uses of `arg' *)
        InsertUse (arg, opnd)
      ELSIF (opnd. arg # arg) THEN
        Append (opnd. nextOpnd)
      END
    END Append;
  
  BEGIN
    Append (instr. opndList)
  END UniqueOperand;

PROCEDURE (opnd: Opnd) DeleteOperand*;
(* Removes the operand `opnd' from the list of `opnd. instr's operands.  *)
  VAR
    prev: Opnd;
  BEGIN
    DeleteUse (opnd);
    IF (opnd. instr. opndList = opnd) THEN
      opnd. instr. opndList := opnd. nextOpnd
    ELSE
      prev := opnd. instr. opndList;
      WHILE (prev. nextOpnd # opnd) DO
        prev := prev. nextOpnd
      END;
      prev. nextOpnd := opnd. nextOpnd
    END;
    opnd. nextOpnd := NIL;
    opnd. instr := NIL
  END DeleteOperand;

PROCEDURE (opnd: Opnd) ReplaceOperand* (arg: Usable);
  BEGIN
    DeleteUse (opnd);
    InsertUse (arg, opnd)
  END ReplaceOperand;

PROCEDURE (of: Usable) ReplaceUses* (with: Usable);
(* Replaces all uses of `of' with `with'.  
   pre: ~((of IS Object) OR (of IS Struct)) *)
  VAR
    use, nextUse: Opnd;
  BEGIN
    ASSERT (~((of IS Object) OR (of IS Struct)));
    (* if `of' is Object or Struct, then operands that may not be used as value
       (eg, adr operand, access operand) may be replaced, nuking their 
       instructions *)
    use := of. useList;
    WHILE (use # NIL) DO
      nextUse := use. nextUse;
      DeleteUse (use);
      InsertUse (with, use);
      use := nextUse
    END
  END ReplaceUses;


PROCEDURE (instr: Instruction) AppendResult* (location: Location; type: Struct): Result;
  PROCEDURE Append (VAR res: Result): Result;
    BEGIN
      IF (res = NIL) THEN
        NEW (res);
        InitResult (res, type);
        res. location := location;
        (* append `res' to list of results of `instr' *)
        res. nextResult := NIL;
        res. instr := instr;
        RETURN res
      ELSE
        RETURN Append (res. nextResult)
      END
    END Append;
  
  BEGIN
    RETURN Append (instr. nextResult)
  END AppendResult;

PROCEDURE (res: Result) DeleteResult*;
(* Removes `res' from its instruction's result list. 
   pre: ~(res IS Instruction)  *)
  VAR
    prev: Result;
  BEGIN
    prev := res. instr;
    WHILE (prev. nextResult # res) DO
      prev := prev. nextResult
    END;
    prev. nextResult := res. nextResult
  END DeleteResult;


PROCEDURE (region: Region) Insert* (instr: Instruction);
(* Appends `instr' to list of instructions of `region'.  If `instr IS Region',
   then it's also inserted into the list of nested regions.  *)
  BEGIN
    instr. region := region;
    (* append `instr' to list of instructions in `region' *)
    instr. nextInstr := NIL;
    instr. prevInstr := region. instrTail;
    IF (region. instrList = NIL) THEN    (* add as first element of list *)
      region. instrList := instr;
      region. instrTail := instr
    ELSE                                 (* append to end of list *)
      region. instrTail. nextInstr := instr;
      region. instrTail := instr
    END;
    WITH instr: Region DO  (* add region to list of regions *)
      instr. nextRegion := region. regionList;
      region. regionList := instr
    ELSE
    END
  END Insert;

PROCEDURE (region: Region) ReverseInstr*;
(* Reverses the instruction list in `region'.  *)
  VAR
    old, new, next: Instruction;
  BEGIN
    new := NIL;
    old := region. instrList;
    WHILE (old # NIL) DO
      IF (old IS Region) THEN
        old(Region). ReverseInstr()
      END;
      next := old. nextInstr;
      old. nextInstr := new;
      IF (new # NIL) THEN
        new. prevInstr := old
      END;
      old. prevInstr := NIL;
      new := old;
      old := next
    END;
    region. instrTail := region. instrList;
    region. instrList := new
  END ReverseInstr;

PROCEDURE RemoveFromInstrList (instr: Instruction);
  BEGIN
    IF (instr. prevInstr = NIL) THEN
      instr. region. instrList := instr. nextInstr
    ELSE
      instr. prevInstr. nextInstr := instr. nextInstr
    END;
    IF (instr. nextInstr = NIL) THEN
      instr. region. instrTail := instr. prevInstr
    ELSE
      instr. nextInstr. prevInstr := instr. prevInstr
    END;
    instr. nextInstr := NIL;
    instr. prevInstr := NIL
  END RemoveFromInstrList;

PROCEDURE RemoveFromRegionList (instr: Region);
  VAR
    prev: Region;
  BEGIN
    (* remove `instr' from region list *)
    IF (instr. region. regionList = instr) THEN
      instr. region. regionList := instr. nextRegion
    ELSE
      prev := instr. region. regionList;
      WHILE (prev. nextRegion # instr) DO
        prev := prev. nextRegion
      END;
      prev. nextRegion := instr. nextRegion
    END;
    instr. nextRegion := NIL
  END RemoveFromRegionList;

PROCEDURE (n: Node) Greg*(): GlobalRegion;
  VAR
    region: Region;
  BEGIN
    WITH n: Opnd DO
      region := n. instr. region
    | n: Region DO
      region := n
    | n: Instruction DO
      region := n. region
    | n: Result DO
      region := n. instr. region
    END;
    WHILE (region. region # NIL) DO
      region := region. region
    END;
    RETURN region(GlobalRegion)
  END Greg;


PROCEDURE (instr: Instruction) Delete*;
(* Removes `instr' from list of instructions of `instr. region'.  If `instr IS
   Region', then it's also removed from the list of nested regions after its 
   local instructions have been deleted.  All operands are removed.  *)
  VAR
    next, nested: Instruction;
    greg: GlobalRegion;
  BEGIN
    (* if deleting enter or exit instruction: clear greg reference *)
    IF (instr. opcode = Opc.enter) OR (instr. opcode = Opc.exit) THEN
      greg := instr. region. Greg();
      IF (instr. opcode = Opc.enter) THEN
        greg. enter := NIL
      ELSE
        greg. exit := NIL
      END
    END;
    (* get rid of operands and remove them from use lists *)
    WHILE (instr. opndList # NIL) DO
      instr. opndList. DeleteOperand();
    END;
    IF (instr. region # NIL) THEN
      RemoveFromInstrList (instr)
    END;
    IF (instr IS Region) THEN
      (* remove all instructions in the region `instr' *)
      nested := instr(Region). instrList;
      WHILE (nested # NIL) DO
        next := nested. nextInstr;
        nested. Delete();
        nested := next
      END;
      IF (instr. region # NIL) THEN
        RemoveFromRegionList (instr(Region))
      END
    END;
    instr. region := NIL;
    instr. marker := -1
  END Delete;

PROCEDURE (to: Region) MoveInstruction* (instr: Instruction);
  BEGIN
    RemoveFromInstrList (instr);
    IF (instr IS Region) THEN
      RemoveFromRegionList (instr(Region))
    END;
    instr. region := NIL;
    to. Insert (instr)
  END MoveInstruction;

PROCEDURE (to: Region) MoveInstructions* (from: Region);
  BEGIN
    WHILE (from. instrList # NIL) DO
      to. MoveInstruction (from. instrList)
    END
  END MoveInstructions;

PROCEDURE (toInstr: Instruction) MoveResultList* (prevResult: Result);
(* Moves list of results starting at `prevResult.nextResult' to the end of
   the result list of `toInstr'.  *)
  VAR
    end: Result;
  BEGIN
    end := toInstr;
    WHILE (end. nextResult # NIL) DO
      end := end. nextResult
    END;
    end. nextResult := prevResult. nextResult;
    prevResult. nextResult := NIL;
    end := end. nextResult;
    WHILE (end # NIL) DO
      end. instr := toInstr;
      end := end. nextResult
    END
  END MoveResultList;

PROCEDURE (res: Result) MoveResultToEnd*;
(* Move `res' to the end of the result list.  *)
  VAR
    prev: Result;
  BEGIN
    IF (res. nextResult # NIL) THEN
      prev := res. instr;
      WHILE (prev. nextResult # res) DO
        prev := prev. nextResult
      END;
      prev. nextResult := res. nextResult;
      
      WHILE (prev. nextResult # NIL) DO
        prev := prev. nextResult
      END;
      res. nextResult := NIL;
      prev. nextResult := res
    END
  END MoveResultToEnd;

PROCEDURE (opnd: Opnd) MoveOperandToEnd*;
(* Move `opnd' to the end of the operand list.  *)
  VAR
    prev: Opnd;
    instr: Instruction;
  BEGIN
    IF (opnd. nextOpnd # NIL) THEN
      instr := opnd. instr;
      IF (instr. opndList = opnd) THEN
        instr. opndList := opnd. nextOpnd;
        prev := instr. opndList
      ELSE
        prev := instr. opndList;
        WHILE (prev. nextOpnd # opnd) DO
          prev := prev. nextOpnd
        END;
        prev. nextOpnd := opnd. nextOpnd
      END;
      
      WHILE (prev. nextOpnd # NIL) DO
        prev := prev. nextOpnd
      END;
      opnd. nextOpnd := NIL;
      prev. nextOpnd := opnd
    END
  END MoveOperandToEnd;

PROCEDURE TransferResultList* (prevRes: Result; VAR saved: Result; restore: BOOLEAN);
  BEGIN
    IF restore THEN
      prevRes. nextResult := saved;
      saved := NIL
    ELSE
      saved := prevRes. nextResult;
      prevRes. nextResult := NIL
    END
  END TransferResultList;

PROCEDURE TransferOperandList* (prevOpnd: Opnd; VAR saved: Opnd; restore: BOOLEAN);
  BEGIN
    IF restore THEN
      prevOpnd. nextOpnd := saved;
      saved := NIL
    ELSE
      saved := prevOpnd. nextOpnd;
      prevOpnd. nextOpnd := NIL
    END
  END TransferOperandList;


PROCEDURE (region: Region) CreateInstruction* (opcode: INTEGER; 
                              type: Struct; pos: LONGINT): Instruction;
  VAR
    instr: Instruction;
  BEGIN
    NEW (instr);
    InitInstruction (instr, type, pos);
    instr. opcode := opcode;
    region. Insert (instr);
    RETURN instr
  END CreateInstruction;

PROCEDURE (merge: Merge) CreateGate* (opcode: INTEGER; var: Object; type: Struct): Gate;
  VAR
    gate: Gate;
  BEGIN
    NEW (gate);
    InitInstruction (gate, type, undefPos);
    gate. opcode := opcode;
    gate. var := var;
    gate. oldValue := NIL;
    gate. Operand (merge);
    merge. Insert (gate);
    RETURN gate
  END CreateGate;
  
PROCEDURE InitGuard* (guard: Guard; cond: Usable; opcode: INTEGER; pos: LONGINT);
  BEGIN
    InitRegion (guard, pos);
    guard. opcode := opcode;
    guard. Operand (cond)
  END InitGuard;

PROCEDURE CreateGuard* (cond: Usable; opcode: INTEGER; pos: LONGINT): Guard;
  VAR
    guard: Guard;
  BEGIN
    NEW (guard);
    InitGuard (guard, cond, opcode, pos);
    RETURN guard
  END CreateGuard;

PROCEDURE CreateMerge* (opcode: INTEGER): Merge;
  VAR
    merge: Merge;
  BEGIN
    NEW (merge);
    InitRegion (merge, undefPos);
    merge. opcode := opcode;
    RETURN merge
  END CreateMerge;


PROCEDURE (type: Struct) OpenDimensions*(): INTEGER;
(* Number of "open" dimensions of `type'.  Zero if `type' isn't an open array
   (or no array at all).  *)
  BEGIN
    IF (type. form # strOpenArray) THEN
      RETURN 0
    ELSE
      RETURN type. base. OpenDimensions()+1
    END
  END OpenDimensions;

PROCEDURE (type: Struct) Dimensions*(): INTEGER;
(* Number of dimensions of `type'.  Zero if `type' isn't an array, 1 if `type'
   is a one-dimensioned array (of fixed size or open), increasing by 1 for 
   every nested array type.  *)
  BEGIN
    IF (type. form # strOpenArray)  & (type. form # strArray) THEN
      RETURN 0
    ELSE
      RETURN type. base. Dimensions()+1
    END
  END Dimensions;

PROCEDURE (instr: Instruction) GetResult* (var: Addressable; attrib: INTEGER): Result;
(* Locates result of given symbolic location.  *)
  VAR
    res: Result;
  BEGIN
    res := instr. nextResult;
    WHILE (res # NIL) & ((res. location = NIL) OR 
                         (res. location(SymLocation). var # var) OR
                         (res. location(SymLocation). attrib # attrib)) DO
      res := res. nextResult
    END;
    RETURN res
  END GetResult;

PROCEDURE (instr: Instruction) LastResult*(): Result;
  VAR 
    res: Result;
  BEGIN
    res := instr;
    WHILE (res. nextResult # NIL) DO
      res := res. nextResult
    END;
    RETURN res
  END LastResult;

PROCEDURE (instr: Instruction) GetOperand* (var: Addressable; attrib: INTEGER): Opnd;
(* Locates operand of given symbolic location.  *)
  VAR 
    opnd: Opnd;
  BEGIN
    opnd := instr. opndList;
    WHILE (opnd # NIL) & ((opnd. location = NIL) OR
                          (opnd. location(SymLocation). var # var) OR
                          (opnd. location(SymLocation). attrib # attrib)) DO
      opnd := opnd. nextOpnd
    END;
    RETURN opnd
  END GetOperand;

PROCEDURE (instr: Instruction) LastOperand*(): Opnd;
  VAR 
    opnd: Opnd;
  BEGIN
    opnd := instr. opndList;
    IF (opnd = NIL) THEN
      RETURN NIL
    ELSE
      WHILE (opnd. nextOpnd # NIL) DO
        opnd := opnd. nextOpnd
      END;
      RETURN opnd
    END
  END LastOperand;

PROCEDURE (instr: Instruction) SetOpndSymLoc* (obj: Addressable);
(* Sets the symbolic location of `instr's last operand to `obj'.  *)
  VAR
    opnd: Opnd;
  BEGIN
    opnd := instr. LastOperand();
    opnd. location := CreateSymLocation (obj, symLocObject)
  END SetOpndSymLoc;

PROCEDURE (opnd: Opnd) OpndType*(): Struct;
(* Retrieves the type of the given operand.  *)
  VAR
    arg: Usable;
  BEGIN
    arg := opnd. arg;
    WITH arg: Const DO
      RETURN arg. type
    | arg: Object DO
      RETURN arg. type
    | arg: Result DO
      RETURN arg. type
    | arg: Struct DO
      RETURN arg
    END
  END OpndType;

PROCEDURE (instr: Instruction) ArgumentIndex* (arg: Usable): INTEGER;
(* Returns the position of the first operand of `instr' that has `arg' as 
   argument.  Result is -1 if no such operand exists.  The first operand has
   the index 0.  *)
  VAR
    i: INTEGER;
    opnd: Opnd;
  BEGIN
    i := 0;
    opnd := instr. opndList;
    WHILE (opnd # NIL) & (opnd. arg # arg) DO
      opnd := opnd. nextOpnd;
      INC (i)
    END;
    IF (opnd = NIL) THEN
      RETURN -1
    ELSE
      RETURN i
    END
  END ArgumentIndex;

PROCEDURE (opnd: Opnd) OperandIndex*(): INTEGER;
(* Returns the position of `opnd' in its instruction's operand list.  The first
   operand has the index 0.  *)
  VAR
    i: INTEGER;
    ptr: Opnd;
  BEGIN
    i := 0;
    ptr := opnd. instr. opndList;
    WHILE (ptr # opnd) DO
      INC (i);
      ptr := ptr. nextOpnd
    END;
    RETURN i
  END OperandIndex;

PROCEDURE (instr: Instruction) NthOperand* (nth: INTEGER): Opnd;
(* Returns the `nth' operand of `instr'.
   pre: 0 <= nth < Number of operands of `instr'.  *)
  VAR
    opnd: Opnd;
  BEGIN
    opnd := instr. opndList;
    WHILE (nth # 0) DO
      opnd := opnd. nextOpnd;
      DEC (nth)
    END;
    RETURN opnd
  END NthOperand;

PROCEDURE (instr: Instruction) NthArgument* (nth: INTEGER): Usable;
(* Returns the argument of the `nth' operand of `instr'.
   pre: 0 <= nth < Number of operands of `instr'.  *)
  VAR
    opnd: Opnd;
  BEGIN
    opnd := instr. opndList;
    WHILE (nth # 0) DO
      opnd := opnd. nextOpnd;
      DEC (nth)
    END;
    RETURN opnd. arg
  END NthArgument;

PROCEDURE (instr: Instruction) NthResult* (nth: INTEGER): Result;
(* Returns the `nth' result of `instr'.
   pre: 0 <= nth < NumOfResults (instr). *)
  VAR
    res: Result;
  BEGIN
    res := instr;
    WHILE (nth # 0) DO
      res := res. nextResult;
      DEC (nth);
    END;
    RETURN res;    
  END NthResult;

PROCEDURE (result: Result) ResultIndex*(): INTEGER;
(* Returns the position of `result' in its instruction's result list. The first
   result of an instruction (i.e. the instruction itself) has the index 0. *)
  VAR
    i: INTEGER;
    ptr: Result;
  BEGIN
    i := 0;
    ptr := result. instr;
    WHILE (ptr # result) DO
      INC (i);
      ptr := ptr. nextResult;
    END;
    RETURN i;    
  END ResultIndex;

PROCEDURE (instr: Instruction) NumOfOperands*(): INTEGER;
(* Returns the number of operands of `instr'. *)
  VAR
    num: INTEGER;
    opnd: Opnd;
  BEGIN
    num := 0;
    opnd := instr. opndList;
    WHILE (opnd # NIL) DO
      INC (num);
      opnd := opnd. nextOpnd;
    END;
    RETURN num;
  END NumOfOperands;

PROCEDURE (instr: Instruction) NumOfResults*(): INTEGER;
(* Returns the number of results of `instr'. *)
  VAR
    num: INTEGER;
    res: Result;
  BEGIN
    num := 0;
    res := instr;
    WHILE (res # NIL) DO
      INC (num);
      res := res. nextResult;
    END;
    RETURN num;
  END NumOfResults;


PROCEDURE (region: Region) EnterInstr*(): Instruction;
(* Locates the enter instruction of `region's global region.  Result is NIL if
   `region=NIL' or no enter instruction exists.  *)
  BEGIN
    region := region. Greg();
    RETURN region(GlobalRegion). enter
  END EnterInstr;

PROCEDURE (region: Region) ExitInstr*(): Instruction;
(* Locates the exit instruction of `region's global region.  Result is NIL if
   `region=NIL' or no exit instruction exists.  *)
  BEGIN
    region := region. Greg();
    RETURN region(GlobalRegion). exit
  END ExitInstr;

PROCEDURE (toMove: Instruction) MoveBehind* (prevInstr: Instruction);
(* Moves instruction `toMove' in the region's instruction list right behind the
   instruction `prevInstr', or to the start of the list if `prevInstr=NIL'.
   Note that the region list is not modified.
   pre: (prevInstr = NIL) OR (prevInstr. region = toMove. region)  *)
  VAR
    region: Region;
  BEGIN
    region := toMove. region;
    RemoveFromInstrList (toMove);
    IF (prevInstr = NIL) THEN            (* move to start of list *)
      toMove. prevInstr := NIL;
      toMove. nextInstr := region. instrList;
      IF (region. instrList # NIL) THEN
        region. instrList. prevInstr := toMove
      ELSE
        region. instrTail := toMove 
      END;
      region. instrList := toMove
    ELSE
      toMove. prevInstr := prevInstr;
      toMove. nextInstr := prevInstr. nextInstr;
      prevInstr. nextInstr := toMove;
      IF (toMove. nextInstr # NIL) THEN
        toMove. nextInstr. prevInstr := toMove
      ELSE
        region. instrTail := toMove
      END
    END
  END MoveBehind;

PROCEDURE (toMove: Instruction) MoveInFront* (nextInstr: Instruction);
(* Moves instruction `toMove' in the region's instruction list right in front
   of the instruction `nextInstr', or to the end of the list if
   `nextInstr=NIL'. 
   Note that the region list is not modified.
   pre: (nextInstr = NIL) OR (nextInstr. region = toMove. region)  *)
  VAR
    region: Region;
  BEGIN
    region := toMove. region;
    RemoveFromInstrList (toMove);
    IF (nextInstr = NIL) THEN            (* move to end of list *)
      toMove. nextInstr := NIL;
      toMove. prevInstr := region. instrTail;
      IF (region. instrTail # NIL) THEN
        region. instrTail. nextInstr := toMove
      ELSE
        region. instrList := toMove 
      END;
      region. instrTail := toMove
    ELSE
      toMove. nextInstr := nextInstr;
      toMove. prevInstr := nextInstr. prevInstr;
      nextInstr. prevInstr := toMove;
      IF (toMove. prevInstr # NIL) THEN
        toMove. prevInstr. nextInstr := toMove
      ELSE
        region. instrList := toMove
      END
    END
  END MoveInFront;


PROCEDURE (region: Region) ClearInfo* (m: LONGINT);
(* Sets `info' fields of all results in `region' to NIL, and the `marker' 
   fields to `m'.  *)
  VAR
    instr: Instruction;
    result: Result;
  BEGIN
    region. info := NIL;
    region. marker := m;
    instr := region. instrList;
    WHILE (instr # NIL) DO
      WITH instr: Region DO
        instr. ClearInfo (m)
      ELSE
        result := instr;
        WHILE (result # NIL) DO
          result. info := NIL;
          result. marker := m;
          result := result. nextResult
        END
      END;
      instr := instr. nextInstr
    END
  END ClearInfo;

PROCEDURE (region: Region) ClearInstrInfo* (m: LONGINT);
(* Sets `info' fields of all instruction results in `region' to NIL, and the
   `marker' fields to `m'.  Regions are not modified.  *)
  VAR
    instr: Instruction;
    result: Result;
  BEGIN
    instr := region. instrList;
    WHILE (instr # NIL) DO
      WITH instr: Region DO
        instr. ClearInstrInfo (m)
      ELSE
        result := instr;
        WHILE (result # NIL) DO
          result. info := NIL;
          result. marker := m;
          result := result. nextResult
        END
      END;
      instr := instr. nextInstr
    END
  END ClearInstrInfo;

PROCEDURE (region: Region) ClearRegionInfo* (m: LONGINT);
(* Sets `info' fields of all regions in `region' to NIL, and the
   `marker' fields to `m'.  Instructions are not modified.  *)
  BEGIN
    region. info := NIL;
    region. marker := m;
    region := region. regionList;
    WHILE (region # NIL) DO
      region. ClearRegionInfo (m);
      region := region. nextRegion
    END
  END ClearRegionInfo;


PROCEDURE NewConst (type: Struct; hash: LONGINT): Const;
  VAR
    c: Const;
  BEGIN
    NEW (c);
    InitConst (c, type);
    c. nextConst := constList[hash];
    constList[hash] := c;
    RETURN c
  END NewConst;

PROCEDURE GetIntConst* (value: LONGINT; type: Struct): Const;
  VAR
    c: Const;
    hash: LONGINT;
  BEGIN
    hash := value MOD sizeConstList;
    c := constList[hash];
    WHILE (c # NIL) & ((c. type # type) OR (c. int # value)) DO
      c := c. nextConst
    END;
    IF (c = NIL) THEN
      c := NewConst (type, hash);
      c. int := value
    END;
    RETURN c
  END GetIntConst;

<* PUSH; Warnings := FALSE *>
PROCEDURE GetRealConst* (value: LONGREAL; type: Struct): Const;
  VAR
    c: Const;
    hash: LONGINT;
  BEGIN
    SYSTEM.MOVE (SYSTEM.ADR (value), SYSTEM.ADR (hash), SIZE (LONGINT));
    hash := hash MOD sizeConstList;
    c := constList[hash];
    WHILE (c # NIL) & ((c. type # type) OR (c. real # value)) DO
      c := c. nextConst
    END;
    IF (c = NIL) THEN
      c := NewConst (type, hash);
      c. real := value
    END;
    RETURN c
  END GetRealConst;
<* POP *>

PROCEDURE GetSetConst* (value: SET; type: Struct): Const;
  VAR
    c: Const;
    hash: LONGINT;
  BEGIN
    (* clip value against allowed bit range; this way no invalid constants, 
       e.g. a SET8 constant containing element `15', can be created *)
    value := value * setMask[type. form - strSet8];
    hash := SYSTEM.VAL (LONGINT, value) MOD sizeConstList;
    
    c := constList[hash];
    WHILE (c # NIL) & ((c. type # type) OR (c. set # value)) DO
      c := c. nextConst
    END;
    IF (c = NIL) THEN
      c := NewConst (type, hash);
      c. set := value
    END;
    RETURN c
  END GetSetConst;

PROCEDURE GetStringConst* (VAR value: ARRAY OF CHAR; len: LONGINT;
                           type: Struct): Const;
(* Get string constant of the requested type.  Character sequence of type
   LONGCHAR must be passed to `value' as 2 CHARs, putting the MSB first.

   Note: Actually `value' could be marked with NO_COPY; unfortunately the 
   compiler "sees" that this procedure modifies a heap object containing a 
   character array, but is not smart enough to "see" that this character array
   cannot be passed to `value'.  Such are the limits of conservative 
   approximations :-/  *)
  VAR
    c: Const;
    hash, i, j, sizeChar: LONGINT;
  
  PROCEDURE Neq (VAR a, b: ARRAY OF CHAR; lena, lenb: LONGINT): BOOLEAN;
    BEGIN
      IF (lena # lenb) THEN
        RETURN TRUE
      ELSE
        FOR i := 0 TO lena*sizeChar-1 DO
          IF (a[i] # b[i]) THEN
            RETURN TRUE
          END
        END;
        RETURN FALSE
      END
    END Neq;
  
  BEGIN
    sizeChar := struct[type. form+(strChar8-strStringConst8)]. size;
    
    j := len;
    IF (j > 4) THEN j := 4 END;
    i := 0; hash := 0;
    WHILE (i < j) DO
      hash := hash*128+ORD(value[sizeChar*i+(sizeChar-1)]); INC (i)
    END;
    hash := hash MOD sizeConstList;
    
    c := constList[hash];
    WHILE (c # NIL) & 
          ((c. type # type) OR Neq (c. string^, value, c. int, len)) DO
      c := c. nextConst
    END;
    IF (c = NIL) THEN
      c := NewConst (type, hash);
      c. int := len;
      NEW (c. string, (len+1)*sizeChar);
      FOR i := 0 TO len*sizeChar-1 DO
        c. string[i] := value[i]
      END;
      FOR i := 0 TO sizeChar-1 DO
        c. string[len*sizeChar+i] := 0X
      END
    END;
    RETURN c
  END GetStringConst;

PROCEDURE GetRangeConst* (from, to: LONGINT; type: Struct): Const;
  VAR
    c: Const;
  BEGIN
    c := constRange;
    WHILE (c # NIL) & ((c. int # from) OR (c. int2 # to)) DO
      c := c. nextConst
    END;
    IF (c = NIL) THEN
      NEW (c);
      InitConst (c, NIL);
      c. type := type;
      c. int := from;
      c. int2 := to;
      c. nextConst := constRange;
      constRange := c
    END;
    RETURN c
  END GetRangeConst;

PROCEDURE ConvertString* (const: Const; to: SHORTINT): Const;
  CONST
    sizeBuffer =  2*1024;
  VAR
    b: POINTER TO ARRAY OF CHAR;
    i, n, char: LONGINT;
    buffer:  ARRAY sizeBuffer OF CHAR;
    
  PROCEDURE To8 (VAR buffer, source: ARRAY OF CHAR; len: LONGINT): Const;
    VAR
      i: LONGINT;
    BEGIN
      FOR i := 0 TO len-1 DO
        buffer[i] := source[2*i+1]
      END;
      RETURN GetStringConst (buffer, len, struct[strStringConst8])
    END To8;
  
  PROCEDURE To16 (VAR buffer, source: ARRAY OF CHAR; len: LONGINT): Const;
    VAR
      i: LONGINT;
    BEGIN
      FOR i := 0 TO len-1 DO
        buffer[2*i] := 0X;
        buffer[2*i+1] := source[i]
      END;
      RETURN GetStringConst (buffer, len, struct[strStringConst16])
    END To16;
  
  BEGIN
    IF (to = const. type. form) THEN  (* nothing to do *)
      RETURN const
    END;
    
    IF (to = strStringConst8) THEN  (* from = strStringConst16 *)
      (* if converting from string16 to string8, all characters must by valid
         char8 values *)
      FOR i := 0 TO const. int-1 BY 2 DO
        char := LONG (ORD (const. string[2*i]))*256 + ORD (const. string[2*i+1]);
        IF (char > ORD (MAX (CHAR))) THEN  (* should be: > StdTypes.maxChar *)
          RETURN NIL
        END
      END;
      
      n := struct[strChar8]. size * (const. int+1)
    ELSE
      n := struct[strChar16]. size * (const. int+1)
    END;
    
    IF (n > sizeBuffer) THEN
      NEW (b, n);
      IF (to = strStringConst8) THEN
        RETURN To8 (b^, const. string^, const. int)
      ELSE
        RETURN To16 (b^, const. string^, const. int)
      END
    ELSE
      IF (to = strStringConst8) THEN
        RETURN To8 (buffer, const. string^, const. int)
      ELSE
        RETURN To16 (buffer, const. string^, const. int)
      END
    END
  END ConvertString;
  
PROCEDURE CompareStrings* (c1, c2: Const): LONGINT;
(* Compares two string constants of arbitrary type.  Result:
     <0: c1 < c2
     =0: c1 = c2
     >0: c1 > c2
   pre: (c1. type. form IN {strStringConst8, strStringConst16}) &
        (c1.type = c2. type)  *)
  VAR
    i, j: LONGINT;
  BEGIN
    ASSERT ((c1. type. form IN {strStringConst8, strStringConst16}) &
            (c1. type = c2. type));
    j := c1. int;
    IF (j < c2. int) THEN
      j := c2. int
    END;
    IF (c1. type. form = strStringConst16) THEN
      j := j*2
    END;
    FOR i := 0 TO j-1 DO
      IF (c1. string[i] # c2. string[i]) THEN
        RETURN ORD (c1. string[i]) - ORD (c2. string[i])
      END
    END;
    RETURN (c1. int - c2. int)
  END CompareStrings;

PROCEDURE FreeConsts*;
(* Frees all constants in the internally managed list that aren't in use.  Not
   in use means that a given constant doesn't appear in some piece of GSA code
   and that it isn't part of some module's symbol table.  *)
  VAR
    i: INTEGER;
    
  PROCEDURE FreeList (VAR c: Const);
    BEGIN
      IF (c # NIL) THEN
        FreeList (c. nextConst);
        IF (c. useList = NIL) & ~c. preserve THEN
          c. type := NIL;
          c. string := NIL;
          c := c. nextConst
        END
      END
    END FreeList;
  
  BEGIN
    FOR i := 0 TO sizeConstList-1 DO
      FreeList (constList[i])
    END;
    FreeList (constRange)
  END FreeConsts;

PROCEDURE SortRanges* (caseGuard: Guard);
(* Brings range operands into ascending order and merges as many operands as
   possible.  *)
  VAR
    range: Const;
    list, newList, next, opnd, ptr, end: Opnd;
  
  PROCEDURE Insert (VAR list: Opnd; opnd: Opnd);
    BEGIN
      IF (list = NIL) THEN
        opnd. nextOpnd := NIL;
        list := opnd
      ELSIF (opnd. arg(Const). int < list. arg(Const). int) THEN
        opnd. nextOpnd := list;
        list := opnd
      ELSE
        Insert (list. nextOpnd, opnd)
      END
    END Insert;
  
  BEGIN
    (* create sorted list of operands *)
    list := caseGuard. opndList. nextOpnd;
    newList := NIL;
    WHILE (list # NIL) DO
      next := list. nextOpnd;
      Insert (newList, list);
      list := next
    END;
    (* merge neighbouring ranges into a single one *)
    list := caseGuard. opndList;
    opnd := newList;
    WHILE (opnd # NIL) DO
      end := opnd;
      WHILE (end. nextOpnd # NIL) &
            (end. nextOpnd. arg(Const). int = end. arg(Const). int2+1) DO
        end := end. nextOpnd
      END;
      next := end. nextOpnd;
      
      IF (end # opnd) THEN
        (* new range value *)
        range := GetRangeConst (opnd. arg(Const). int, end. arg(Const). int2,
                                opnd. arg(Const). type);
        (* delete old range values *)
        ptr := opnd;
        WHILE (ptr # end) DO
          DeleteUse (ptr);
          ptr := ptr. nextOpnd
        END;
        DeleteUse (end);
        (* set new range for `opnd' *)
        InsertUse (range, opnd)
      END;
      
      (* add `opnd' to guard's operand list *)
      list. nextOpnd := opnd;
      opnd. nextOpnd := NIL;
      list := opnd;
      opnd := next
    END
  END SortRanges;


PROCEDURE (obj: Object) Module*(): Object;
(* Given an object designating a procedure, a type-bound procedure, or the
   module, return the module the declaration is part of.  Use function
   `SymbolTable.Module' for arbitrary objects.  *)
  VAR
    receiverType: Struct;
  BEGIN
    WHILE (obj. mode # objModule) OR (obj. localTo(Object). moduleId >= 0) DO
      CASE obj. mode OF
      | objModule, objProc:
        obj := obj. localTo(Object)
      | objTBProc:
        receiverType := obj. data(Object). type;
        obj := receiverType. obj. localTo(Object)
      END
    END;
    RETURN obj
  END Module;


PROCEDURE (greg: GlobalRegion) NumberDominanceTree*;
(* Create information for dominance tests `Dominates' and `DominatesNR'.
   Creating and moving regions within `greg' invalidates the information. *)
  VAR
    counter: INTEGER;
  
  PROCEDURE RecNumberTree (reg: Region; VAR counter: INTEGER);
    VAR
      region: Region;
    BEGIN
      reg. rangeL := counter;
      region := reg. regionList;
      WHILE (region # NIL) DO
        RecNumberTree (region, counter);
        region := region. nextRegion
      END;
      reg. rangeH := counter;
      INC (counter)
    END RecNumberTree;
  
  BEGIN
    counter := MIN(INTEGER);
    RecNumberTree (greg, counter)
  END NumberDominanceTree;

PROCEDURE (x: Region) Dominates* (y: Region): BOOLEAN;
(* TRUE, iff `x = y' or `y' is directly or indirectly nested in `x'.
   pre: Dominance information has been created by running `NumberDominanceTree'
        and hasn't been invalidated in the meantime. *)
  BEGIN
    RETURN (x. rangeL <= y. rangeH) & (y. rangeH <= x. rangeH)
  END Dominates;

PROCEDURE (x: Region) DominatesNR* (y: Region): BOOLEAN;
(* TRUE, iff `y' is directly or indirectly nested in `x', but not if `x = y'.
   pre: Dominance information has been created by running `NumberDominanceTree'
        and hasn't been invalidated in the meantime. *)
  BEGIN
    RETURN (x. rangeL <= y. rangeH) & (y. rangeH < x. rangeH)
  END DominatesNR;


(* these procedure were previously defined in Opcode.Mod: *)

PROCEDURE (instr: Instruction) Class*(): INTEGER;
  BEGIN
    RETURN (instr. opcode DIV Opc.sizeClass)
  END Class;

PROCEDURE (instr: Instruction) Subclass*(): INTEGER;
  BEGIN
    RETURN (instr. opcode MOD Opc.sizeClass)
  END Subclass;

PROCEDURE OperatorSubclass* (type: Struct; typeForm: SHORTINT): SHORTINT;
(* Map a type onto an operator subclass.  If `type' is not NIL, it is used
   for the calculation, otherwise the decision is based in the `form' id 
   (from Data.Struct. form).  *)
  VAR
    subclass: SHORTINT;
  BEGIN
    IF (type # NIL) THEN
      typeForm := type. form
    END;
    
    (* determine subclass of operator *)
    CASE typeForm OF
    | strBoolean, strChar8, strByte, strSet8:
      subclass := Opc.subclSU
    | strShortInt:
      subclass := Opc.subclS
    | strInteger:
      subclass := Opc.subclI
    | strSet16, strChar16:
      subclass := Opc.subclIU
    | strLongInt:
      subclass := Opc.subclL
    | strHugeInt:
      subclass := Opc.subclLL
    | strPtr, strNil, strPointer, strProc:
      subclass := Opc.subclAdr  (* equals Opc.subclL or Opc.subclLL *)
    | strReal:
      subclass := Opc.subclR
    | strLongReal:
      subclass := Opc.subclD
    | strSet32:
      subclass := Opc.subclLU
    | strSet64:
      subclass := Opc.subclLLU
    | strStringConst8:
      subclass := Opc.subclStr
    | strStringConst16:
      subclass := Opc.subclLStr
    | strArray:
      IF (type. base. form = strChar16) THEN
        subclass := Opc.subclLStr
      ELSE
        subclass := Opc.subclStr
      END
    ELSE
      subclass := Opc.subclS
    END;
    RETURN subclass
  END OperatorSubclass;

PROCEDURE (opnd: Opnd) ValueOperand*(): BOOLEAN;
(* Determines if the value of operand `opnd' is used as input to the 
   instruction or if the operand is used to define something different.  
   Example:
   The instruction `adr' can take an object as operand; but not the object's
   value is used, but rather the object describes which address is to be 
   returned.  *)
  VAR
    ptr, first: Opnd;
    opn: INTEGER;
  BEGIN
    IF (opnd. instr. opcode DIV Opc.sizeClass = Opc.classMerge) THEN
      opn := 1
    ELSE
      first := opnd. instr. opndList;
      CASE opnd. instr. opcode OF
      | Opc.adr, Opc.gate, Opc.new, Opc.accessNonlocal, Opc.accessVarParam,
        Opc.updateHeap, Opc.updateNonlocal, Opc.updateVarParam, Opc.zero:
        opn := 1
      | Opc.call:
        RETURN (first. nextOpnd # opnd) &
               (first. nextOpnd. nextOpnd # opnd)
      | Opc.accessField:
        opn := 3
      | Opc.accessHeap:
        RETURN (first # opnd)
      | Opc.tbProcAdr:
        RETURN (first. nextOpnd # opnd) &
               (first. nextOpnd. nextOpnd # opnd)
      ELSE
        RETURN TRUE
      END
    END;
    ptr := opnd. instr. opndList;
    WHILE (ptr # NIL) & (opn > 1) DO
      DEC (opn);
      ptr := ptr. nextOpnd
    END;
    RETURN (opn # 1) OR (ptr # opnd)
  END ValueOperand;

PROCEDURE (opnd: Opnd) PassThroughOperand*(): BOOLEAN;
(* Determines if the value of operand `opnd' is used to contruct parts of the
   instruction result.
   Example:
   The update-field instruction takes a record as first operand and builds the
   result by using the record's value and replacing a single field.  This 
   access to the record variable should not be considered as access to an
   undefined value.  *)
  VAR
    ptr: Opnd;
    opn: INTEGER;
  BEGIN
    CASE opnd. instr. opcode OF
    | Opc.stringCopy, Opc.structCopy, Opc.updateField, Opc.updateElement: 
      opn := 1
    | Opc.updateMem:
      opn := 1
    | Opc.updateNonlocal, Opc.updateVarParam, Opc.updateHeap:
      opn := 3
    ELSE
      RETURN FALSE
    END;
    ptr := opnd. instr. opndList;
    WHILE (ptr # NIL) & (opn > 1) DO
      DEC (opn);
      ptr := ptr. nextOpnd
    END;
    RETURN (opn = 1) & (ptr = opnd)
  END PassThroughOperand;

PROCEDURE (r: Region) RegionMerge*(): Merge;
(* Returns the merge region into which control proceeds after this region is
   finished.  This coincides with the merge that would contain gates generated
   by the region `r'.  Note that there may be serveral merges that have `r' 
   for an operand, but only one that combines the flow of control leaving `r' 
   with another region.
   Result is NIL if no such merge exists.  
   post: For result M holds: M is not a loop merge with `r' for first operand.
         `r' is an operand of M.  *)
  VAR
    use: Opnd;
  BEGIN
    use := r. useList;
    WHILE (use # NIL) & 
          ((use. instr. opcode DIV Opc.sizeClass # Opc.classMerge) OR
           (use. instr. opcode = Opc.mergeLoop) &
           (use. instr. opndList. arg = r)) DO
      use := use. nextUse
    END;
    IF (use = NIL) THEN
      RETURN NIL
    ELSE
      RETURN use. instr(Merge)
    END
  END RegionMerge;

PROCEDURE (instr: Instruction) MayTrap*(): BOOLEAN;
(* Returns TRUE if `instr' may trigger a run-time error when fed with the wrong
   values.  This predicate does not consider the `instrMayTrap' flag, it just
   inspects the opcode.  An instruction that might trap can't be moved out of
   a guard without checking that it's arguments are guaranteed to be valid
   outside the guard, too.  *)
  VAR
    opc: INTEGER;
  BEGIN
    opc := instr. opcode;
    RETURN (opc = Opc.call) OR (opc = Opc.arrayLength) OR 
           (opc = Opc.typeTag) OR (opc = Opc.boundIndex) OR
           (opc = Opc.boundRange) OR (opc = Opc.typeGuard) OR
           (opc = Opc.typeAssert) OR (opc = Opc.bit) OR
           (opc = Opc.accessHeap) OR (opc = Opc.updateHeap) OR 
           (opc = Opc.accessMem) OR (opc = Opc.updateMem) OR
           (opc DIV Opc.sizeClass = Opc.classTrap)
  END MayTrap;



PROCEDURE (region: Region) CreateAdrInstr* (arg: Usable; pos: LONGINT): Instruction;
  VAR
    instr: Instruction;
  BEGIN
    instr := region. CreateInstruction (Opc.adr, struct[strAddress], pos);
    instr. Operand (arg);
    RETURN instr
  END CreateAdrInstr;

PROCEDURE (region: Region) CreateDyadicOp* (opcode: INTEGER; type: Struct;
                     opnd1, opnd2: Usable; pos: LONGINT): Instruction;
  VAR
    instr: Instruction;
  BEGIN
    instr := region. CreateInstruction (opcode, type, pos);
    instr. Operand (opnd1);
    instr. Operand (opnd2);
    RETURN instr
  END CreateDyadicOp;

PROCEDURE (region: Region) CreateTypeCast* (value: Usable; toType: Struct): Instruction;
  VAR
    instr: Instruction;
  BEGIN
    instr := region. CreateInstruction (Opc.typeCast, toType, undefPos);
    instr. Operand (value);
    RETURN instr
  END CreateTypeCast;



(* Retrieve various info from a call instruction.  Note that these procedures
   expect that `tb-proc-adr' instructions are still present in the intermediate
   code.  *)
   
PROCEDURE (call: Instruction) GetReceiver*(): Object;
(* Given a call instruction, return its receiver, or NIL if its a normal 
   procedure call.  *)
  VAR
    arg: Usable;
    obj: Object;
  BEGIN
    arg := call. opndList. nextOpnd. nextOpnd. arg;
    IF (arg # constUndef) THEN  (* procedure call *)
      obj := arg(Object);
      IF (obj. mode = objTBProc) THEN
        RETURN obj. data(Object)
      ELSE
        RETURN NIL
      END
    ELSE  (* call of procedure variable *)
      RETURN NIL
    END
  END GetReceiver;

PROCEDURE (opnd: Opnd) GetFormalParam*(): Object;
(* Given the operand of a call instruction, return the formal parameter (or
   the receiver) it corresponds to.  Note that multiple operands (value, 
   address, type tag, length) can correspond to a single formal parameter/
   receiver.  NIL is returned if the operand models one of the additional 
   side-effects.  *)
  VAR
    obj, param: Object;
    paramOpnd: Opnd;
    
  PROCEDURE OpndPartOfParam (param: Object; VAR paramOpnd: Opnd): BOOLEAN;
  (* Returns TRUE if the operand `opnd' is part of the argument list for the 
     formal parameter `param'.  Otherwise moves `paramOpnd' forward in the 
     operand list until the next formal parameter's section is reached.  *)
    VAR
      prevOpnd: Opnd;
    BEGIN
      IF (paramOpnd = opnd) OR (param. mode = objRestParam) THEN
        (* this is the first operand of a sequence belonging to the given
           formal parameter, or all following operands are mapped to the
           rest parameter *)
        RETURN TRUE
      ELSE  (* move `paramOpnd' beyond the sequence of `param' operands *)
        REPEAT
          prevOpnd := paramOpnd;
          IF (prevOpnd = opnd) THEN
            RETURN TRUE
          END;
          paramOpnd := paramOpnd. nextOpnd
        UNTIL (paramOpnd = NIL) OR
              (paramOpnd. location(SymLocation). var # param) OR
              (prevOpnd. location(SymLocation). attrib >=
               paramOpnd. location(SymLocation). attrib);
        RETURN FALSE
      END
    END OpndPartOfParam;
  
  BEGIN
    ASSERT (opnd. instr. opcode = Opc.call);
    IF (opnd. location # NIL) &
       (opnd. location(SymLocation). var IS Object) THEN
      obj := opnd. location(SymLocation). var(Object);

      paramOpnd := opnd. instr. NthOperand (3);
      param := opnd. instr. GetReceiver();
      IF (param # NIL) & OpndPartOfParam (param, paramOpnd) THEN
        RETURN param
      ELSE
        param := opnd. instr. opndList. nextOpnd. arg(Struct). decl;
        WHILE (param # NIL) DO
          IF OpndPartOfParam (param, paramOpnd) THEN
            RETURN param
          END;
          param := param. rightObj
        END
      END
    END;
    RETURN NIL
  END GetFormalParam;

BEGIN
  FOR i := 0 TO strNone DO struct[i] := NIL END;
  FOR i := 0 TO sizeConstList-1 DO constList[i] := NIL END;
  NEW (constNil);
  NEW (constUndef);
  constRange := NIL;
END Data.
