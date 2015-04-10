(*	$Id: liboo2c.Mod,v 1.19 2000/03/01 11:28:29 ooc-devel Exp $	*)
MODULE liboo2c [LIBRARY "oo2c" "14:0:2"; INTERFACE "C"];
<* Warnings := FALSE *>
   
IMPORT
  (* basic string handling *)
  Ascii,            (* standard short character names for control chars *)
  CharClass,        (* classification of values of type CHAR *)
  Strings,          (* facilities to manipulate strings *)
  LongStrings,      (* LONGCHAR version of module `Strings' *)
  
  (* integer/string conversion *)
  ConvTypes,        (* common types used in the string conversion modules *)
  IntConv,          (* low-level integer/string conversions *)
  IntStr,           (* integer-number/string conversions *)
  
  (* I/O subsystem *)  
  Channel,          (* defines abtract channel type *)
  StdChannels,      (* interface to standard in, out, and err channels *)
  Files,            (* file access *)
  ProgramArgs,      (* facilities to access program arguments *)
  TextRider,        (* textual input from and output to the above channels *)
  BinaryRider,      (* binary input from and output to the above channels *)
  In,               (* simple interface to standard input *)
  Out,              (* simple interface to standard output *)
  Err,              (* simple interface to standard error channel *)
  Log,              (* simple logging facility to standard error channel *)
  
  (* math libs, real/string conversion *)
  LowReal,          (* access to underlying properties of type REAL *)
  RealMath,         (* mathematical functions for REAL *)
  RealConv,         (* low-level REAL/string conversions *)
  RealStr,          (* REAL/string conversions *)
  
  LowLReal,         (* access to underlying properties of type LONGREAL *)
  LRealMath,        (* mathematical functions for LONGREAL *)
  LRealConv,        (* low-level LONGREAL/string conversions *)
  LRealStr,         (* LONGREAL/string conversions *)
  
  Integers,         (* arbitrary precision integer operations *)
  Reals,            (* arbitrary precision floating point operations *)
  
  (* complex math *)
  ComplexMath,      (* mathematical functions for type COMPLEX *)
  LComplexMath,     (* mathematical functions for type LONGCOMPLEX *)
  
  (* time stamps and intervalls, conversion between string and time *)
  Time,             (* manipulation of time stamps and time intervalls *)
  JulianDay,        (* calendar based on julian day count *)
  Calendar,         (* conversion between time stamp and calendar/clock *)
  SysClock,         (* reading and setting the system clock *)

  (* random number generator *)
  RandomNumbers,    (* preliminary version *)

  (* miscellaneous *)
  Exception,        (* exception handling *)
  Signal,           (* installing signal handlers for Unix *)
  
  (* localization stuff *)
  Locales,
  LocStrings,
  LocNumConv,
  LocNumStr,
  LocTextRider,
  LocText,

  (* Oakwood compliant modules *)
  OakStrings,       (* string manipulation *)
  OakFiles,         (* file access *)
  OakIn,            (* basic functions for formatted input *)
  OakOut,           (* basic functions for formatted output *)
  OakMath,          (* mathematical functions for REAL *)
  OakMathL,         (* mathematical functions for LONGREAL *)
(*OakXYplane: simple graphics device, only available with X11 *)

  (* Miscellaneous 
     Note: these modules are _not_ part of the official OOC library (yet) *)
  Msg,
  Kernel,
  Types;
  
(* 
There are a number of modules that were used in this implementation, but 
that aren't part of the OOC library.  These modules are not guaranteed 
to be available on all systems, or are very system specific.  They shouldn't 
be used in portable programs:
  o PosixFileDescr
  o LongInts
*)

END liboo2c.
