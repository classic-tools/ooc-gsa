(* 	$Id: Opcode.Mod,v 1.84 2000/07/20 18:24:20 ooc-devel Exp $	 *)
MODULE Opcode;
(*  This modules defines opcodes for GSA instructions.
    Copyright (C) 1995-2000  Michael van Acken

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
This file lists all legal opcodes for instructions.  Every GSA instruction is 
an instance of `Data.Instruction'.  The opcode is stored in 
`Data.Instruction.opcode'.  Most instructions have exactly one result, but in
general an instruction may have an arbitrary number of results.  A result is 
always a value and has to be considered a distinct copy that isn't modified in
any way later on (e.g. assigning to a record field creates a copy of the 
record's value with the field modified accordingly).

Some words regarding the handling of aliasing of arbitrary memory accesses:
The pseudo variable $mem represents the whole memory of the current process.  
All other variables and the heap are embedded in $mem.  Normally there is no
need to actually make sure that variables are stored to memory or loaded from
memory.  Problems arise whenever this matter can't be ignored.  
  Previously forcing variables into or from memory was done by the dedicated
instructions `collect' and `reclaim'.  Well, that's history.  The instructions
had unusual properties and generally didn't fit in smoothlessly with the normal
instructions.  The result was lots of ugly code scattered all over the compiler
to handle these special cases.
  The list of instructions dealing with $mem is quite short.  Reading from 
$mem: procedure call, GET, PUT, BIT, and MOVE.  Writing to $mem: procedure 
call, PUT, and MOVE.  An instruction `foo' reading from $mem will have this 
format:
  ... := foo ... <mem> <store> <var>...
Where <mem> and <store> are the current values of the pseudo variables $mem 
and $store.  <var> is a list of (values of) locally declared variables (this 
includes value parameters, but excludes variable parameters), their respective
location attribute refers to their variable object.  No other operands follow
after <mem>.
An instruction `foo' writing to $mem will have this format:
  ... <mem> <store> <var>... := foo ...
The results have the same properties as the operand of the corresponding name.
Note: For any result beyond <mem> there is a corresponding operand of the same
location.
  Any variables appearing in on operand or result list after $mem+$store are
local scalar variables of the current procedure.  They have their location 
attribute set to their symbol table object to indicate that they have to be 
forced into memory (when appearing as operand) or retrieved from memory (when
appearing as result).  
  If $mem appears in the result list of an enter instruction it will be the
very last result.  Likewise if $mem appears in the operand list of an exit 
instruction it will be the very last operand.


The second pseudo variable, $store, serves to model read and write accesses to
variables outside the scope of the current procedure.  Three classes of
variables are part of $store: nonlocal variables, variable parameters, and heap
objects.  Operations on these kinds of variables are implemented by special
opcodes: access-nonlocal, access-var-param, access-heap, their update
counterparts, and (of course) procedure calls.  Note that the exact content of
$store differs between procedures: what might be a nonlocal variable or a
variable parameter for one procedure can be a local variable for another.
  A procedure lists all nonlocal objects it reads from in the result list of
its enter instruction.  For every nonlocal variable it has a result whose
location attribute is set to the variable's symbol table object, and for every
heap object a result whose location is the type description (D.Struct) of the
object.  Likewise all updates of nonlocal objects appear as operands of the
procedure's exit instruction.  A procedure call duplicates nonlocal access
information in its own operand and result lists; if necessary it will also
contain a $store operand and possibly a $store result.
  Writing to a variable parameter may change the value of a nonlocal variable,
or that of a heap object, and vice versa.  These aliasing effects are also
handled by means of $store.  The chain of $store updates as emitted by the
frontend is guaranteed to execute all updates to $store in the order they are
written in the source code.
  The Brandis paper suggests to chain heap accesses by means of pseudo 
variables for every type of heap object.  This was dropped in favour of the
single pseudo variable $store.  The reason for this is that separate access
chains by type can't deal with aliasing effects between variable parameters and
heap objects and therefore can't replace $store.  On the other hand they do not
any information that isn't already encoded in $store.  Therefore they were
eliminated from OOC.
*)
  
CONST
  enter* = 1;
(* <result>... := enter 
  This instruction represents the procedure prolog.  It provides the interface
  to parameter values and nonlocal variables.  The result list contains results
  for formal parameters (see doc/ParameterPassing), followed by results for 
  each nonlocal variable (and every structure on the heap) accessed.  The 
  front-end sets the location field of every result to a symbolic reference 
  (an instance of Data.SymLocation) to the parameter, variable, or structure 
  that provides its value.  *)

  exit* = 2;
(* exit <opnd>...
  This instruction represents the procedure epilog.  It summarizes the side 
  effects of the procedure.  Its operand list contains the result value, 
  followed by values for changed variable parameters, nonlocal variables, and
  heap objects.  The front-end sets the location field of every operand to a 
  symbolic reference (an instance of Data.SymLocation) to the parameter, 
  variable, or structure that'll hold the respective operand's value after the
  procedure has terminated.  *)

  call* = exit+1;
(* "<result-list>... [mem] := call <address> <formal-type> <proc-obj>
                            <parameter>... <nonlocal-ref>... [mem]"
  Calls the given (normal or type-bound) procedure or function.
  pre: <address> is the procedure's address.  <formal-type> describes the 
    formal parameter list of the call (a value of type Data.Struct).  
    <proc-obj> holds for a direct procedure call (normal or type-bound) the
    procedure object that is called, and is `Data.constUndef' if it activates a
    procedure variable.  Note that for type-bound procedures <proc-obj> refers
    to the static procedure that is used in the source code, but during runtime
    the actual value of <address> may refer to any redefinition of <proc-obj>.
    
    <parameter> is a list of values passed as parameters to the procedure.
    The location attribute (Data.SymLocation. var) of every actual parameter
    (and its implicit operands like type tag and length) refers to the 
    respective formal parameter in <formal-type>.  There are two exceptions to
    this rule: if the actual parameter is a local variable (or value parameter)
    of the caller _and_ the formal one is a variable parameter, then the 
    location of the operand that holds the variable's value is the local 
    variable (to force it into memory); actual parameters passed to the rest 
    parameter `...' have no location (i.e. it is NIL).
    
    <nonlocal-ref> is a list of the (current values of) variables or structures
    that are accessed nonlocally by the procedure.  If any of the nonlocal
    references accesses an object that isn't local to the caller, an operand
    with the value of $store is part of the operand list.

    If the called instruction reads from $mem, then the nonlocal references are
    followed by an operand for $mem, for $store, and possibly a number of local
    scalar variables.  The variables have their location attribute set to their
    symbol table object to indicate that they have to be forced into memory.
    
  result: A function's result value is the instruction itself (i.e. the result
    with `index' 0).  <result-list> is a list of nonlocal assignments of the 
    procedure (its side effects).  If any of the nonlocal side-effects changes
    an object that isn't local to the caller, then a new value of $store is 
    part of the result list.
    
    If the called procedure writes to $mem, then the nonlocal side-effects are
    followed by a result for $mem, a result for $store, and possibly a number
    of values for local scalar variables.  The variables have their location 
    attribute set to their symbol table object to indicate that they have to 
    be read from memory with the next access.  
  
  See also the notes at the beginning of this file about the handling of $mem.  *)

  createStore* = exit+4;
(* "$store := create-store"
  Initializes pseudo variable $store.  Result is the initial (empty, clear) 
  value for $store.  This instruction is always part of the global region and 
  is executed before any references to $store occur.  Has always the flag
  `instrIsDisabled' set.  *)
  
  deleteStore* = exit+5;
(* "delete-store <store>"
  Frees pseudo variable $store.  <store> is the value of $store that is valid
  at the end of the global region.  This instruction is always part of the 
  global region and is placed after the last assignment to $store.  For this
  instruction the flag `instrNoDead' is always set.  *)
  

  
  adr* = deleteStore+1;  
(* "adr <usable>"
  Calculates the address of an object.  Since the actual address calculations
  will change when a procedure is inlined, the front-end can only insert these
  symbolic address values.  The back-end has to replace them by the actual 
  addresses after procedure inlining has been done.
  Note that only the addresses of local variables (or local value parameters)
  of the greg are determined by an address instruction.  For nonlocal variables
  or variable parameters the addresses are derived from the enter instruction.
  Therefore for any instruction "adr x" with x denoting an object of mode 
  objVar, x is a local variable of the procedure.
  pre: <usable> is an `Object' of mode objVar or objProc, or it is a `Const' 
    with type `strStringConst', or it is a record type (a `Struct') designating
   the address of the record's type descriptor
  result: address of the usable (or the type descriptor)  *)
  
  arrayLength* = adr+1;
(* "array-length <address> <dim>"
  Retrieves the length of an open array object on the heap.
  pre: <address> is the value of a pointer type with an open array as base 
    type, <dim> (an INTEGER value) is the dimension whose length is requested.
    <dim> is greater or equal to 0 and less than the number of open dimensions
    in the pointer's base type.
  result: A LONGINT value with the number of elements of the array in dimension
    <dim>.  The instruction should trap if the flag `Data.instrCheckNil' is set
    and <address> is NIL.  *)

  typeTag* = adr+2;
(* "type-tag <address>" 
  Retrieves the type tag of an record object on the heap.
  pre: <address> is the value of a pointer type with a record base type.
  result: A LONGINT value representing the type tag.
  The type tag is usually an address.  The type tag of a static record is 
  calculated with `adr <struct>', where <struct> is the record's type (a value
  of type `Struct').  The instruction should trap if the flag 
  `Data.instrCheckNil' is set and <address> is NIL.  *)

  tbProcAdr* = adr+3;  
(* "tb-proc-adr <type-tag> <static-type> <tb-proc>"
  Calculates the dynamic address (entry point) of a type-bound procedure.
  pre: <type-tag> is type descriptor that has to be used; <static-type> is the
    static record type (Data.Struct) of the designator on which the procedure 
    was called; <tb-proc> is the type-bound procedure, a value of type 
    `Object'.  The field `tbProc. offset' contains the procedure's index.  
    The first tb proc has the index 0, if the index is known.  For index 
    values that can only be assigned after the whole module has been parsed,
    the field `offset' holds negative values.
    
    For back-ends that support virtual method tables in the first field
    of a record instance: <static-type> has the flag `Data.structVTableField'
    set, and <type-tag> is the address of the record on the heap.
  result: The procedure's address (LONGINT).  *)
  
  

(*
The following instructions (except for type-test) correspond to runtime checks.
They apply a predicate to their first operand and generate a trap if the test
fails.  Otherwise they return the value of their first operand for their
result.  These instructions are inserted into the GSA code even if their
respective runtime check is disabled.  In this case they are marked with the
flag `Data.instrIsDisabled' and are removed in as dead code in the last phase
of the standard optimizations, when DeadCodeElimination.Eliminate' is called
with TRUE as its second parameter.
*)

  boundIndex* = tbProcAdr+1;
(* "bound-index <index> <length>"
  Checks that the value of <index> is in the range [0..<length>-1].
  pre: <index> is an array index of integer type, <length> the length of the 
    dimension being indexed (a LONGINT value).
  result: Traps if the index is outside [0..<length>-1].  Otherwise the result
    is <index>.  *)
  
  boundRange* = boundIndex+1;
(* "bound-range <element-index> <set-size>"
  Checks that the value of <element-index> is in the range [0..<set-size>-1].
  pre: <element-index> is an set element of integer type, <set-size> the size 
    of the set in bits.  The latter is a SHORTINT constant, usually 32, but set
    variants with 8, 16, or 64 bits are accessible as SYSTEM types to ease
    interfacing with foreign languages.
  result: Traps if the element index is outside [0..<length>-1].  Otherwise 
    the result is <element-index>.  *)
  
  typeTest* = boundIndex+2;
(* "type-test <var> <var-type-tag> <type-tag> <ext-level> 
  Tests the type of a variable against one of its extensions.
  pre: <var-type-tag> is the variable's type tag, <type-tag> the tag of the 
    type against which the variable is tested. <ext-level> is the number of
    direct base types of the type (zero means no base types).  <var> is the
    value of the variable (pointer or record) being tested.
  post: TRUE iff the variable's type is an extension of the rhs type, ie iff
    its base type at level <ext-level> is <type-tag>.  *)

  typeGuard* = boundIndex+3;
(* "type-guard <var> <var-type-tag> <type-tag> <ext-level> 
  Guards the type of a variable against one of its extensions.
  pre: <var> is the variable's value; <var-type-tag> is the variable's type 
    tag; <type-tag> the tag of the type against which the variable is tested. 
    <ext-level> is the number of direct base types of the type (zero means no 
    base types).  
  post: Traps if the variable's type isn't an extension of the rhs type, ie iff
    its base type at level <ext-level> isn't <type-tag>.  Otherwise the result
    is <var>.  *)

  typeAssert* = boundIndex+4;
(* "type-assert <var> <var-type-tag> <type-tag>"
  Asserts that the variable is of a given type.
  pre: <var> is the variable's value; <var-type-tag> is the variable's type 
    tag; <type-tag> the tag of the type against which the variable is tested. 
  post: Traps if the variable's type isn't equal to the rhs type.  Otherwise 
    the result is <var>.  
  This instruction is similar to a type guard.  But it isn't tested if the 
  actual type is an extension of the required one, but rather for type 
  identity.  This instruction is generated when assigning a record to a record
  variable whose dynamic type may differs from its static one.  *)

  
  
  
  zero* = typeAssert+1;
(* "zero <var> <address>"
  Used to initialize structured variables to zero.  The variable is passed as 
  first parameter, followed by its address.
  result: An `initialized' (zeroed) value of the given type. *)
  
  copy* = zero+1;
(* "copy <usable>" 
  Creates a copy of the operand.
  pre: <usable> is a constant or the current value of a variable.
  result: The value of the operand.
  This is a redundant instruction for plain GSA, since in GSA every result of 
  an instruction is a copy of its own.  The front-end inserts such instructions
  to keep usage of different variables apart during the construction of GSA.  
  Copy propagation is run right after the front-end is finished, removing all 
  copy instructions.
  The back-end (at least the oo2c incarnation) usually introduces copy 
  instructions of its own to deal with aliasing effects on local scalar 
  variables of a procedure.  *)
  
  gate* = zero+2;
(* "gate <merge> <value1> <value2> ..."
  Merges the different values a variable may obtain following differnt paths of
  control flow.
  pre: <merge> is a reference to a merge instruction.  If the merge has n
    operands <opnd1>, <opnd2>, etc, then this gate has n+1 operands.
  result: If this gate was reached following the operand <opndX> of the merge,
    then the result is <valueX>, i.e. the value corresponding to the region
    by which the merge was reached.  *)
  
  bit* = zero+3;
(* "bit <address> <bit-index> <mem> <store> <var...>"
  Opcode for SYSTEM.BIT.
  pre: <address> is a memory address, <bit-index> the number of the bit being 
    queried.
  post: TRUE iff the bit is set.  If <address> is a pointer to ARRAY OF SET,
    then the result is (<bit-index> MOD 32) IN <address>[<bit-index> DIV 32].*)

  typeCast* = zero+4;
(* "type-cast <value>"
  pre: <value> is an expression of arbitrary type.
  result: <value> interpreted as if it would be of the instruction's type. 
  If the initial cast had a simple variable as second argument, the operand's
  location is set to refer to this variable.  *)

  stringCopy* = zero+5;
(* "string-copy <dest> <dest-adr> <dest-len> <src> <src-adr>"
  Copies a string value to a variable.
  pre: <dest> is the value of the destination variable, <dest-adr> its address,
    <dest-len> its length.  <src> is the source value, <src-adr> its address.
    If destination isn't a proper Oberon array (i.e. there is no length 
    information available), then <dest-len> is the integer constant with
    the value of `StdTypes.maxLongInt'.  
  result: A copy of <src>, truncated if it contains <dest-len> or more
    characters. 
  Note: Both source and destination may be CHAR or LONGCHAR arrays.  Copying
    from a larger to a smaller character type is not allowed, but the other
    direction is possible.  In this case the character values must be 
    extended on the fly.  *)

  structCopy* = zero+6;
(* "struct-copy <dest> <dest-adr> <dest-len> <src> <src-adr>"
  Copies a structured value (record, array, or complex) to a variable.  This 
  instruction is generated as part of every assignment statement `x := y' whose
  source and destination are of a structured type, and therefore has to copy a
  memory block.
  pre: <dest> is the value of the destination variable, <dest-adr> its address,
    <dest-len> its length (an integer constant).  <src> is the source value, 
    <src-adr> its address.
  result: The value of <src>.  
  Note: If the destination is a character array, and the source a string
    constant, then <dest-len> is actually the length of the string (including
    the trailing 0X).  *)




  new* = structCopy+1;
(* "new <type> <length>..."
  Creates new object on heap.
  pre: <type> is the object's type, <length> the length of dimension 0, 1, etc.
  result: The address of the new object.  *)
  
  newBlock* = new+1;
(* "new-block <size>"
  Creates new object on heap (SYSTEM.NEW).
  pre: <size> is the new block's size in bytes.
  result: The address of the new object.  *)

  move* = new+2;
(* "move <src-adr> <dest-adr> <size>"
  Moves <size> bytes from <src-adr> to <dest-adr>.  *)


(* ---------------------------------------------------------------------- *)
(* ---------------------------------------------------------------------- *)

CONST
  sizeClass* = 16;
  (* an instruction opcode `opc' is constructed by
       opc := class(operator) * sizeClass + subclass(operator)
     given an opcode `opc' then
       the operator class is `opc DIV sizeClass'
       the operator type is `opc MOD sizeClass'  *)

(* ---------------------------------------------------------------------- *)
(* access and update *)

CONST
  subclField* = 0;
  subclElement* = 1;
  subclHeap* = 2;
  subclNonlocal* = 3;
  subclVarParam* = 4;
  subclMem* = 5;
  
CONST
  classAccess* = 2;
  baseAccess* = classAccess*sizeClass;
  accessField* = baseAccess+subclField;
(* "access-field <r-value> <address> <field>"
  pre: <r-value> is the record value being accessed, which may be the current 
    value of a variable or of a structure.  <field> the field being accessed. 
    <address> is the address of the record field.
  result: The value of the field being accessed.  *)
  accessElement* = baseAccess+subclElement;
(* "access-element <r-value> <address> <index>"
  pre: <r-value> is the array value being accessed, which may be the current 
    value of a variable or of a structure.  <index> the number of the element
    being accessed.  <address> is the address of the array element.
  result: The value of the element being accessed.  *)
  accessHeap* = baseAccess+subclHeap;
(* "access-heap <type> <address> <store>"
  pre: <type> is the type description (Data.Struct) of the object being 
    accessed, <address> its memory location.  <store> is the current value of 
    the pseudo variable $store.
  result: The value of the object being accessed.
  Note that this instruction is generated each time a record or array pointer 
  is dereferenced.  The instruction should trap if <address> is NIL and the
  flag `instrCheckNil' is set.  *)
  accessNonlocal* = baseAccess+subclNonlocal;
(* "access-nonlocal <variable> <address> <store>" 
  pre: <variable> is a variable object (Data.Object, _not_ its value), 
    <address> the variable's address, and <store> the current value of the
    pseudo variable $store.
  result: The variable's value.
  This instruction is created for every access to a nonlocal variable except 
  the very first one.  The first access uses the result of the enter 
  instruction corresponding to the variable.  A later optimization step tries
  to eliminate as much of these instructions as possible.  Accesses to
  variable's global to a module are always non-local, even if they are placed
  in the module's body.  *)
  accessVarParam* = baseAccess+subclVarParam;
(* "access-var-param <var-param> <var-address> <store>"
  pre: <var-param> is a variable parameter object (Data.Object, _not_ its 
    value), <var-address> the parameter's address (a result of the region's 
    enter instruction), and <store> the current value of $store.
  result: The parameter's value.
  This instruction is created for every access to a variable parameter except 
  the very first one.  The first access uses the result of the enter 
  instruction corresponding to the parameter.  A later optimization step tries
  to eliminate as much of these instructions as possible.  *)
  accessMem* = baseAccess+subclMem;
(* "access-mem <address> <mem> <store> <var...>"
  Reads from memory.
  pre: <address> is a memory location (type is LONGINT), <mem> the current 
    value of the pseudo variable $mem.  
  result: The memory contents at <address>.
  The accessed item's type is stored in `Instruction.type'.  This instruction
  corresponds to SYSTEM.GET, likewise update-mem corresponds to SYSTEM.PUT.
  The back-end may introduce additional access-mem/update-mem instructions.
  Only scalar values can be accessed this way, i.e. it's forbidden to read
  or write a structured value with these instructions.  *)

CONST
  classUpdate* = classAccess+1;
  baseUpdate* = classUpdate*sizeClass;
(* Every update instruction has all operands of the corresponding access 
   instruction plus an additional operand containing the value that has to be 
   stored.  Except for update-mem this additional operand is appended to the
   operand list of the access.
   Note that in the target code update instructions are either noops or they 
   assign an unstructured value.  To move structured values, e.g. when 
   assigning a whole record to a variable, the instruction struct-copy is used.  *)
  updateField* = baseUpdate+subclField;
(* "<new-record> := update-field <r-value> <address> <field> <new-field>" *)
  updateElement* = baseUpdate+subclElement;
(* "<new-array> := update-element <r-value> <address> <index> <new-element>" *)
  updateHeap* = baseUpdate+subclHeap;
(* "<new-store> := update-heap <type> <address> <store> <new-value>" *)
  updateNonlocal* = baseUpdate+subclNonlocal;
(* "<new-store> := update-nonlocal <variable> <address> <store> <new-value>" *)
  updateVarParam* = baseUpdate+subclVarParam;
(* "<new-store> := update-var-param <var-param> <var-address> <store> <new-value>" *)
  updateMem* = baseUpdate+subclMem;
(* "<new-mem> := update-mem <address> <new-value> <mem> <store> <var...>" *)

(* ---------------------------------------------------------------------- *)
(* guards and merges *)

CONST
  (* subclasses for guard *)
  subclFalse* = 0; subclTrue* = 1; subclGreg* = 2; subclCase* = 3;
  (* subclasses for merge *)
  subclIf* = 0; subclCond* = 1; subclLoop* = 2; (*subclCase* = 3;*)
  
CONST
  classGuard* = classUpdate+1;
  baseGuard* = classGuard*sizeClass;
  (* guard opcodes *)
  guardTrue* = baseGuard+subclTrue;      (* operand: boolean value *)
  guardFalse* = baseGuard+subclFalse;    (* operand: boolean value *)
  guardGreg* = baseGuard+subclGreg;      (* operand: TRUE *)
  guardCase* = baseGuard+subclCase;
    (* operands: selection value followed by a list of ranges; the ranges are
       sorted in ascending order, multiple single elements are merged into
       ranges as far as possible *)
  
CONST
  classMerge* = classGuard+1;
  baseMerge* = classMerge*sizeClass;
  (* Merge opcodes.   A merge has a number of regions as operands; for 
     `merge-case' there may be arbitrary many operands, the other merges have 
     exactly two operands.
     
     A non-loop merge can only contain gates.  In other words, a merge-if, 
     merge-cond, or merge-case is either empty, or it contains an arbitrary 
     number of gate instructions.  *)
  mergeIf* = baseMerge+subclIf;
  mergeCond* = baseMerge+subclCond;
  mergeLoop* = baseMerge+subclLoop;
  mergeCase* = baseMerge+subclCase;

(* ---------------------------------------------------------------------- *)

CONST
  classTrap* = classMerge+1;
  baseTrap* = classTrap*sizeClass;
  (* trap opcodes *)
  trapReturn* = baseTrap;
  trapCase* = baseTrap+1;   (* operand: select value *)
  trapAssert* = baseTrap+2; (* operand: trap number *)
  trapHalt* = baseTrap+3;   (* operand: trap number *)
  trapWith* = baseTrap+4;
  (* if at the place of the trap the variable $mem isn't undefined (i.e. 
     a previous instruction changed its value), then the current value of 
     $mem is added as last argument of the trap instruction *)
  (* a trap-return, trap-case, or trap-with instruction should be ignored by 
     the back-end if its flag `Data.instrIsDisabled' is set *)

(* ---------------------------------------------------------------------- *)
(* ---------------------------------------------------------------------- *)
(* All instructions calculating integer values that have the `instrOverflow' 
   flag set should detect when their evaluation overflows and terminate the 
   program.  The flag isn't set if the user has disabled such checks.  *)
   
CONST
  opcSigned* = FALSE;
  opcUnsigned* = TRUE;
  (* the operator is signed if `ODD(opc) = opcSigned' 
     the operator is unsigned if `ODD(opc) = opcUnsigned'  *)
  subclS* = 0;         (* signed short (1 byte, SHORTINT) *)
  subclSU* = 1;        (* unsigned short (1 byte, CHAR, BOOLEAN) *)
  subclI* = 2;         (* signed integer (2 byte, INTEGER) *)
  subclIU* = 3;        (* unsigned integer (2 byte) *)
  subclL* = 4;         (* signed long (4 byte, LONGINT) *)
  subclLU* = 5;        (* unsigned long (4 byte, SET, POINTER, PTR) *)
  subclLL* = 6;        (* signed long long (8 byte, for 64bit systems) *)
  subclLLU* = 7;       (* unsigned long long (8 byte, for 64bit systems) *)
  subclR* = 8;         (* float (4 byte IEEE, REAL) *)
  subclD* = 10;        (* double (8 byte IEEE, LONGREAL) *)
  subclStr* = 12;      (* string, used exclusively for string comparison *)
  subclLStr* = 14;     (* longstring, used exclusively for string comparison *)
  (* Note: There are no subclasses for complex opcodes, since all complex
           operations are reduced to real arithmetic by the front-end *)
  subclAdr* = subclL;  
  (* alias used for address computations, see Data.strAddress *)
     
(* ---------------------------------------------------------------------- *)
(* type conversion *)

CONST  
  (* format: "conv <source-subclass> <source-value>".  The first opnd is the
     subclass of second operand; the destination subclass is part of the
     instruction's opcode; the destination type is stored in `Instruction. 
     type'
     
     Converting a LONGREAL value to REAL via SHORT is a real operation like any
     other.  That is, it has to honor the current rounding mode.  Usually this
     is round to nearest/even, but the program can change this; the compiler 
     assumes this rounding mode for its constant folding.
     
     When converting from real to integer type, rounding towards negative 
     infinity has to be applied.  Such a conversion is caused by the
     application of the ENTIER function, which returns the largest integer not
     greater than the argument.  Ex: ENTIER(-0.4)=-1, _not_ 0 *)
  classConv* = classTrap+1;
  baseConv* = classConv*sizeClass;
  convs* = baseConv+subclS; convsu* = baseConv+subclSU; 
  convi* = baseConv+subclI; conviu* = baseConv+subclIU;
  convl* = baseConv+subclL; convlu* = baseConv+subclLU;
  convll*= baseConv+subclLL;convllu* = baseConv+subclLLU;
  convr* = baseConv+subclR; convd*  = baseConv+subclD;
  
  
(* ---------------------------------------------------------------------- *)
(* arithmetic operators 
   Specification for DIV and MOD that includes negative rhs:
     x=(x div y)*y + (x mod y)
     0 <= (x mod y) < y  _or_  0 >= (x mod y) > y
     Note: x div y = ENTIER (x / y)  *)

CONST  (* numeric addition and pointer arithmetic (addlu) *)
  classAdd* = classConv+1; 
  baseAdd* = classAdd*sizeClass;
  adds* = baseAdd+subclS; addsu* = baseAdd+subclSU; 
  addi* = baseAdd+subclI; addiu* = baseAdd+subclIU;
  addl* = baseAdd+subclL; addlu* = baseAdd+subclLU;
  addll*= baseAdd+subclLL;addllu*= baseAdd+subclLLU;
  addr* = baseAdd+subclR; addd*  = baseAdd+subclD;

CONST  (* numeric subtraction and pointer arithmetic (sublu) *)
  classSub* = classAdd+1; 
  baseSub* = classSub*sizeClass;
  subs* = baseSub+subclS; subsu* = baseSub+subclSU; 
  subi* = baseSub+subclI; subiu* = baseSub+subclIU;
  subl* = baseSub+subclL; sublu* = baseSub+subclLU;
  subll*= baseSub+subclLL;subllu*= baseSub+subclLLU;
  subr* = baseSub+subclR; subd*  = baseSub+subclD;

CONST  (* numeric multiplication and pointer arithmetic (multlu) *)
  classMult* = classAdd+2; 
  baseMult* = classMult*sizeClass;
  mults* = baseMult+subclS; multsu* = baseMult+subclSU; 
  multi* = baseMult+subclI; multiu* = baseMult+subclIU;
  multl* = baseMult+subclL; multlu* = baseMult+subclLU;
  multll*= baseMult+subclLL;multllu*= baseMult+subclLLU;
  multr* = baseMult+subclR; multd*  = baseMult+subclD;

CONST  (* numeric division, only real *)
  classDivReal* = classAdd+3; 
  baseDivReal* = classDivReal*sizeClass;
  divr* = baseDivReal+subclR; divd*  = baseDivReal+subclD;

CONST  (* numeric division, only integer *)
  classDivInt* = classAdd+4; 
  baseDivInt* = classDivInt*sizeClass;
  divs* = baseDivInt+subclS; divsu* = baseDivInt+subclSU; 
  divi* = baseDivInt+subclI; diviu* = baseDivInt+subclIU;
  divl* = baseDivInt+subclL; divlu* = baseDivInt+subclLU;
  divll*= baseDivInt+subclLL;divllu*= baseDivInt+subclLLU;

CONST  (* modulo operator, only integer *)
  classMod* = classAdd+5; 
  baseMod* = classMod*sizeClass;
  mods* = baseMod+subclS; modsu* = baseMod+subclSU; 
  modi* = baseMod+subclI; modiu* = baseMod+subclIU;
  modl* = baseMod+subclL; modlu* = baseMod+subclLU;
  modll*= baseMod+subclLL;modllu*= baseMod+subclLLU;

CONST  (* negation *)
  classNeg* = classAdd+6; 
  baseNeg* = classNeg*sizeClass;
  negs* = baseNeg+subclS; negi*  = baseNeg+subclI; 
  negl* = baseNeg+subclL; negll* = baseNeg+subclLL;
  negr* = baseNeg+subclR; negd*  = baseNeg+subclD;

(* ---------------------------------------------------------------------- *)
(* operators that are implemented as predefined function procedures *)

CONST  (* absolute value *)
  classAbs* = classNeg+1;
  baseAbs* = classAbs*sizeClass;
  abss* = baseAbs+subclS; absi*  = baseAbs+subclI; 
  absl* = baseAbs+subclL; absll* = baseAbs+subclLL; 
  absr* = baseAbs+subclR; absd*  = baseAbs+subclD;

CONST  (* arithmetic shift *)  
  classAsh* = classAbs+1;
  baseAsh* = classAsh*sizeClass;
  ashs* = baseAsh+subclS; ashi* = baseAsh+subclI;
  ashl* = baseAsh+subclL; ashll* = baseAsh+subclLL;

CONST  (* capitalize character, CHAR and LONGCHAR variant *)
  classCap* = classAbs+2;
  baseCap* = classCap*sizeClass;
  capsu* = baseCap+subclSU;
  capiu* = baseCap+subclIU;

CONST  (* test if number is odd *)
  classOdd* = classAbs+3;
  baseOdd* = classOdd*sizeClass;
  odds* = baseOdd+subclS; oddi*  = baseOdd+subclI; 
  oddl* = baseOdd+subclL; oddll* = baseOdd+subclLL;

CONST  (* logical shift *)
  classLsh* = classAbs+4;
  baseLsh* = classLsh*sizeClass;
  lshs* = baseLsh+subclS; lshsu* = baseLsh+subclSU; 
  lshi* = baseLsh+subclI; lshiu* = baseLsh+subclIU;
  lshl* = baseLsh+subclL; lshlu* = baseLsh+subclLU;
  lshll*= baseLsh+subclLL;lshllu*= baseLsh+subclLLU;

CONST  (* rotation *)
  classRot* = classAbs+5;
  baseRot* = classRot*sizeClass;
  rots* = baseRot+subclS; rotsu* = baseRot+subclSU; 
  roti* = baseRot+subclI; rotiu* = baseRot+subclIU;
  rotl* = baseRot+subclL; rotlu* = baseRot+subclLU;
  rotll*= baseRot+subclLL;rotllu*= baseRot+subclLLU;
  
(* ---------------------------------------------------------------------- *)
(* logical operators *)

CONST  (* bitwise and *)
  classInter* = classRot+1;
  baseInter* = classInter*sizeClass;
  intersectsu* = baseInter+subclSU;
  intersectiu* = baseInter+subclIU;
  intersectlu* = baseInter+subclLU;
  intersectllu* = baseInter+subclLU;

CONST  (* bitwise xor *)
  classSymDiff* = classInter+1;
  baseSymDiff* = classSymDiff*sizeClass;
  symdiffsu* = baseSymDiff+subclSU;
  symdiffiu* = baseSymDiff+subclIU;
  symdifflu* = baseSymDiff+subclLU;
  symdiffllu*= baseSymDiff+subclLLU;
  
CONST  (* bitwise or *)
  classUnion* = classInter+2;
  baseUnion* = classUnion*sizeClass;
  unionsu*  = baseUnion+subclSU;
  unioniu*  = baseUnion+subclIU;
  unionlu*  = baseUnion+subclLU;
  unionllu* = baseUnion+subclLLU;
  
CONST  (* set difference *)
  classDiff* = classInter+3;
  baseDiff* = classDiff*sizeClass;
  diffsu* = baseDiff+subclSU;
  diffiu* = baseDiff+subclIU;
  difflu* = baseDiff+subclLU;
  diffllu*= baseDiff+subclLLU;
  
CONST  (* bitwise complement, monadic *)
  classCompl* = classInter+4;
  baseCompl* = classCompl*sizeClass;
  complsu* = baseCompl+subclSU;
  compliu* = baseCompl+subclIU;
  compllu* = baseCompl+subclLU;
  complllu*= baseCompl+subclLLU;

CONST  (* set SET element *)
  (* 1st opnd: SET value, 2nd opnd: element index (can be any integer type) *)
  classBitSet* = classInter+5;
  baseBitSet* = classBitSet*sizeClass;
  bitsetsu* = baseBitSet+subclSU;
  bitsetiu* = baseBitSet+subclIU;
  bitsetlu* = baseBitSet+subclLU;
  bitsetllu*= baseBitSet+subclLLU;
  
CONST  (* clear SET element *)
  (* 1st opnd: SET value, 2nd opnd: element index (can be any integer type) *)
  classBitClear* = classInter+6;
  baseBitClear* = classBitClear*sizeClass;
  bitclearsu* = baseBitClear+subclSU;
  bitcleariu* = baseBitClear+subclIU;
  bitclearlu* = baseBitClear+subclLU;
  bitclearllu*= baseBitClear+subclLLU;
  
CONST  (* construct SET range *)
  (* 1st opnd, 2nd opnd: element index (can be any integer type) *)
  classBitRange* = classInter+7;
  baseBitRange* = classBitRange*sizeClass;
  bitrangesu* = baseBitRange+subclSU;
  bitrangeiu* = baseBitRange+subclIU;
  bitrangelu* = baseBitRange+subclLU;
  bitrangellu*= baseBitRange+subclLLU;
  
CONST  (* test SET element, boolean result *)
  (* 1st opnd: SET value, 2nd opnd: element index (can be any integer type) *)
  classBitTest* = classInter+8;
  baseBitTest* = classBitTest*sizeClass;
  bittestsu* = baseBitTest+subclSU;
  bittestiu* = baseBitTest+subclIU;
  bittestlu* = baseBitTest+subclLU;
  bittestllu*= baseBitTest+subclLLU;
  
CONST  (* boolean negation, monadic *)
  classNot* = classInter+9;
  baseNot* = classNot*sizeClass;
  notsu* = baseNot+subclSU;

(* ---------------------------------------------------------------------- *)
(* comparison operators; 2 operands (4 if string compare), result is BOOLEAN *)
(* NOTE:
   An operand of a string comparison is either a constant or a char array.
   Instructions that compare strings have 4 (instead of 2) operands.  The
   third and fourth operands hold the address of the first and second argument,
   respectively.  The reason for this is that a string comparison operates on
   address values that have to be a live (for the register allocator) at the 
   place of the compare instruction, and therefore have to appear explicitly as
   operands of the instruction.  *)
   
CONST  (* comparison, test if equal *)
  classEql* = classNot+1;  
  baseEql* = classEql*sizeClass;
  eqls* = baseEql+subclS; eqlsu* = baseEql+subclSU; 
  eqli* = baseEql+subclI; eqliu* = baseEql+subclIU;
  eqll* = baseEql+subclL; eqllu* = baseEql+subclLU;
  eqlll*= baseEql+subclLL;eqlllu*= baseEql+subclLLU;
  eqlr* = baseEql+subclR; eqld*  = baseEql+subclD;
  eqlstr* = baseEql+subclStr;
  eqllstr* = baseEql+subclLStr;
  
CONST  (* comparison, test if not equal *)
  classNeq* = classEql+1;  
  baseNeq* = classNeq*sizeClass;
  neqs* = baseNeq+subclS; neqsu* = baseNeq+subclSU; 
  neqi* = baseNeq+subclI; neqiu* = baseNeq+subclIU;
  neql* = baseNeq+subclL; neqlu* = baseNeq+subclLU;
  neqll*= baseNeq+subclLL;neqllu*= baseNeq+subclLLU;
  neqr* = baseNeq+subclR; neqd*  = baseNeq+subclD;
  neqstr* = baseNeq+subclStr;
  neqlstr* = baseNeq+subclLStr;

CONST  (* comparison, test if less *)
  classLss* = classEql+2;  
  baseLss* = classLss*sizeClass;
  lsss* = baseLss+subclS; lsssu* = baseLss+subclSU; 
  lssi* = baseLss+subclI; lssiu* = baseLss+subclIU;
  lssl* = baseLss+subclL; lsslu* = baseLss+subclLU;
  lssll*= baseLss+subclLL;lssllu*= baseLss+subclLLU;
  lssr* = baseLss+subclR; lssd*  = baseLss+subclD;
  lssstr* = baseLss+subclStr;
  lsslstr* = baseLss+subclLStr;

CONST  (* comparison, test if less or equal *)
  classLeq* = classEql+3;  
  baseLeq* = classLeq*sizeClass;
  leqs* = baseLeq+subclS; leqsu* = baseLeq+subclSU; 
  leqi* = baseLeq+subclI; leqiu* = baseLeq+subclIU;
  leql* = baseLeq+subclL; leqlu* = baseLeq+subclLU;
  leqll*= baseLeq+subclLL;leqllu*= baseLeq+subclLLU;
  leqr* = baseLeq+subclR; leqd*  = baseLeq+subclD;
  leqstr* = baseLeq+subclStr;
  leqlstr* = baseLeq+subclLStr;

CONST  (* comparison, test if greater *)
  classGtr* = classEql+4;  
  baseGtr* = classGtr*sizeClass;
  gtrs* = baseGtr+subclS; gtrsu* = baseGtr+subclSU; 
  gtri* = baseGtr+subclI; gtriu* = baseGtr+subclIU;
  gtrl* = baseGtr+subclL; gtrlu* = baseGtr+subclLU;
  gtrll*= baseGtr+subclLL;gtrllu*= baseGtr+subclLLU;
  gtrr* = baseGtr+subclR; gtrd*  = baseGtr+subclD;
  gtrstr* = baseGtr+subclStr;
  gtrlstr* = baseGtr+subclLStr;

CONST  (* comparison, test if greater or equal *)
  classGeq* = classEql+5;  
  baseGeq* = classGeq*sizeClass;
  geqs* = baseGeq+subclS; geqsu* = baseGeq+subclSU; 
  geqi* = baseGeq+subclI; geqiu* = baseGeq+subclIU;
  geql* = baseGeq+subclL; geqlu* = baseGeq+subclLU;
  geqll*= baseGeq+subclLL;geqllu*= baseGeq+subclLLU;
  geqr* = baseGeq+subclR; geqd*  = baseGeq+subclD;
  geqstr* = baseGeq+subclStr;
  geqlstr* = baseGeq+subclLStr;


CONST
  (* A "no operation" can have arbitry operands and results.  The purpose
     of such an instruction is to do nothing.  Typically, it is used to
     place some kind of information in the GSA code that for some compiler
     component.  *)
  classNoop* = classGeq+1;
  baseNoop* = classNoop*sizeClass;
  noop* = baseNoop;
  noopGateHint* = baseNoop+1;
  (* used by the frontend, removed before any of the code is handed to the
     optimizers or back-end  *)
  

CONST
  maxOpcode* = (classGeq+1)*sizeClass-1;  (* largest opcode in use *)
  


PROCEDURE Commutative* (opcode: INTEGER): BOOLEAN;
(* Returns TRUE if opcode designates a dyadic operation with 
   "a op b = b op a".  *)
  VAR
    class: INTEGER;
  BEGIN
    class := opcode DIV sizeClass;
    CASE class OF
    | classAdd, classMult, classInter, classUnion, classSymDiff,
      classEql, classNeq:
      RETURN TRUE
    ELSE
      RETURN FALSE
    END
  END Commutative;

END Opcode.
