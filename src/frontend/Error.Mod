(* 	$Id: Error.Mod,v 1.24 1999/11/06 15:33:46 ooc-devel Exp $	 *)
MODULE Error;
(*  This modules implements the error reporting.
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
  Out, Strings, Files, IntStr, Filenames, BinaryRider,
  Param := Parameter, Options := ParamOptions, Pragmas := ParamPragmas, 
  StdPragmas, Config;

  
CONST
  eol = 0AX;
  (* end of line marker, used to determine the beginning of a line in
     `ReadErrorList' *)

  suppressDist = 12;
  (* errors are only reported if their file position is at least `suppressDist'
     characters away from the previous error; a value of 0 will emit all 
     errors, 12 is adequate *)
     
TYPE
  (* data structure to hold list of error messages *)
  ErrMsg = POINTER TO ErrMsgDesc;
  ErrMsgDesc = RECORD
    next: ErrMsg;
    num: INTEGER;            (* error number; <0: warning, >0: error *)
    source: Param.String;    (* file name that error refers to *)
    pos: LONGINT;            (* file position *)
    suppressed: LONGINT;     (* interval of suppressed errors after this one *)
    msg: Param.String        (* descriptive text *)
  END;

VAR
  noerr*: BOOLEAN;                      
  (* TRUE if none of the procedures `ErrXXX' has been called yet with a 
     positive error number, ie no error was detected until now *)
  
  errCount*: INTEGER;
  (* number of calls to one of the `ErrXXX' procedures (excluding warnings) *)
  
  verbose-: Options.BooleanOption;
  (* if `verbose. true=TRUE', write strings passed to `VerboseMsg' to stdout, 
     otherwise ignore them *)

  errorMsgs-: Options.StringOption;
  (* name of file with the plain text error messages *)
  
  sourceFile*: Param.String;
  (* the name of the work file used as scanner input, set by `Scanner.Init', 
     cleared by `ParseDecl.Module';  the file name is duplicated in the 
     current module's object (the top of the symbol table) in 
     `mod. data(D.Const). string'  *)
  
  errList: ErrMsg;
  (* all errors are collected in `errList' by calling `StoreError', and are 
     written only to stdout by calling `EmitErrors' *)
     
   
  errDescrList: ErrMsg;                         
  (* list of plain text error descriptions *)

  errListRead: BOOLEAN;
  (* TRUE after `ReadErrorList' has been called *)
  

PROCEDURE ReadErrorList (fileName: ARRAY OF CHAR);
(* Reads error messages from file `fileName'.  If the file can't be read, a
   warning is given.  Each line of the file starting with the character "*"
   is considered to be an error description of the form "\* [0-9]+ : <text>"
   (each " " stand for a possibly emtpy sequence of characters below or 
   equal to " " except eol).  *)
  VAR
    f: Files.File;
    r: BinaryRider.Reader;
    ch: CHAR;
    num, line: INTEGER;
    str: ARRAY 256 OF CHAR;
    i: INTEGER;
    res: Files.Result;
    new: ErrMsg;
    expFileName: Param.Filename;
  
  PROCEDURE SkipWhitespace;
    BEGIN
      WHILE (r. res = BinaryRider.done) & (ch # eol) & (ch <= " ") DO
        r. ReadChar (ch)
      END
    END SkipWhitespace;

  PROCEDURE Err;
    VAR
      str: ARRAY 256 OF CHAR;
      num: ARRAY 32 OF CHAR;
    BEGIN
      str := "Parse error in ";
      Strings.Append (fileName, str);
      Strings.Append (", line ", str);
      IntStr.IntToStr (line, num);
      Strings.Append (num, str);
      Param.FatalError (str)
    END Err;
    
  BEGIN
    errListRead := TRUE;
    Filenames.ExpandPath (expFileName, fileName);
    f := Files.Old (expFileName, {Files.read}, res);
    IF (f = NIL) THEN
      str := "Couldn't read error messages from file ";
      Strings.Append (expFileName, str);
      Param.Warning (str)
    ELSE
      line := 1;
      r := BinaryRider.ConnectReader (f);
      r. ReadChar (ch);
      WHILE (r. res = BinaryRider.done) DO
        IF (ch = "*") THEN
          r. ReadChar (ch);
          SkipWhitespace;
          (* read error number *)
          num := 0;
          WHILE (r. res = BinaryRider.done) & ("0" <= ch) & (ch <= "9") DO
            num := num*10+ORD(ch)-ORD("0"); 
            r. ReadChar (ch)
          END;
          SkipWhitespace;
          
          IF (num = 0) OR (ch # ":") THEN
            Err
          ELSE
            r. ReadChar (ch);
            SkipWhitespace;
            (* read error description *)
            i := 0;
            WHILE (r. res = BinaryRider.done) & (ch >= " ") DO
              IF (i < LEN(str)-1) THEN
                str[i] := ch; INC (i)
              END;
              r. ReadChar (ch)
            END;
            (* remove trailing whitespace *)
            WHILE (i > 0) & (str[i-1] <= " ") DO
              DEC (i)
            END;
            str[i] := 0X;
            
            (* add error to list in `errList' *)
            NEW (new);
            new. next := errDescrList;
            new. num := num;
            new. pos := 0;
            NEW (new. msg, i+1);
            COPY (str, new. msg^);
            errDescrList := new
          END
        END;
        (* move rider to start of next line *)
        WHILE (r. res = BinaryRider.done) & (ch # eol) DO
          r .ReadChar (ch)
        END;
        r. ReadChar (ch);
        INC (line)
      END;
      f. Close
    END
  END ReadErrorList;

PROCEDURE GetErrMsg (num: INTEGER; VAR str: ARRAY OF CHAR);
(* Returns plain text associated with error or warning `num'.  If no such 
   entry can be found (the error list couldn't be loaded or the number does 
   not occur in the file) `str' is filled with a standard "not found"  message.
   If the error file hasn't been read until now, `ReadErrorList' is called. *)
  VAR
    m: ErrMsg;
  BEGIN
    IF ~errListRead THEN
      ReadErrorList (errorMsgs. value^)
    END;
    (* scan list for `num', copy description into `str' *)
    m := errDescrList;
    WHILE (m # NIL) & (m. num # num) DO
      m := m. next
    END;
    IF (m # NIL) THEN
      COPY (m. msg^, str)
    ELSE
      COPY ("(no error message available)", str)
    END
  END GetErrMsg;

PROCEDURE Replace (VAR string, insert: ARRAY OF CHAR);
(* Replaces the first occurence of "%" in `string' with the value of `insert'.
   Nothing happens if `string' doesn't contain a "%". 
   pre: Strings.Length(string)+Strings.Length(insert) < LEN(string) *)
  VAR
    i, j, l, ls: INTEGER;
  BEGIN
    (* find first occurence of "%" in `string' *)
    i := 0;
    WHILE (string[i] # "%") & (string[i] # 0X) DO INC (i) END;
    (* determine length of `string' *)
    ls := i;
    WHILE (string[ls] # 0X) DO INC (ls) END;
    IF (string[i]="%") THEN              (* "%" exists *)
      (* determine length of `insert' *)
      l := 0;
      WHILE (insert[l] # 0X) DO INC (l) END;
      (* make room for `insert' in `string' *)
      j := ls;
      WHILE (j > i) DO string[j+l-1] := string[j]; DEC (j) END;
      (* copy `insert' into `string' *)
      j := 0;
      WHILE (j < l) DO string[i+j] := insert[j]; INC (j) END
    END
  END Replace;


PROCEDURE StoreError (source: Param.String; 
                      pos: LONGINT; num: INTEGER; msg: ARRAY OF CHAR);
(* Inserts new error message at correct position in `errList', or discards
   it if it is a warning or the error is too close to are previous one. 
   `source' is the name of the file the error refers to.  *)
  
  PROCEDURE NewErrMsg (next: ErrMsg): ErrMsg;
    VAR
      errMsg: ErrMsg;
    BEGIN
      NEW (errMsg);
      errMsg. next := next;
      errMsg. num := num;
      errMsg. source := source;
      errMsg. pos := pos;
      errMsg. suppressed := pos;
      NEW (errMsg. msg, Strings.Length (msg)+1);
      COPY (msg, errMsg. msg^);
      RETURN errMsg
    END NewErrMsg;
  
  PROCEDURE Insert (VAR list: ErrMsg; lastErr: ErrMsg);
    BEGIN
      IF (list = NIL) THEN               (* end of error list *)
        list := NewErrMsg (list)
      ELSIF (list. source^ # source^) THEN  
        (* `list' refers to different source file *)
        Insert (list. next, NIL)
      ELSIF (list. pos > pos) THEN
        list := NewErrMsg (list)
      ELSIF (list. next = NIL) OR 
            (list. next. source^ # source^) OR
            (list. next. pos > pos) THEN
        (* `list' is the last entry in the list that refers to the same source
           file and has a position less or equal to `pos' *)
        IF (list. num > 0) THEN
          lastErr := list
        END;
        IF (pos = list. pos) & (list. num = num) & (list. msg^ = msg) THEN
          (* skip error or warning if the file position is already marked with
             exactly the same text *)
        ELSIF (num < 0) OR 
              (lastErr = NIL) OR (lastErr. suppressed+suppressDist <= pos) THEN
          list. next := NewErrMsg (list. next)
        ELSIF (pos > lastErr. suppressed) THEN
          lastErr. suppressed := pos
        END
      ELSIF (list. num > 0) THEN
        Insert (list. next, list)
      ELSE
        Insert (list. next, lastErr)
      END
    END Insert;
  
  BEGIN
    IF (num > 0) OR StdPragmas.warnings. true THEN
      Insert (errList, NIL)
    END
  END StoreError;

PROCEDURE EmitErrors* (includeWarnings: BOOLEAN);
(* Writes list of errors previously stored with `StoreError', sorted by file
   position.  With `includeWarnings=FALSE' all warnings are omitted.  *)
  VAR
    err: ErrMsg;
    lastSource: Param.String;
    
  PROCEDURE WriteError (source: Param.String;
                        pos: LONGINT; num: INTEGER; msg: ARRAY OF CHAR);
  (* Writes error (or warning) with id `num' and description `descr', 
     referring to position `pos' in file `source'.  The first call will write 
     a header containing the name of the source file.  *)
    BEGIN
      IF (lastSource = NIL) OR (lastSource # source) THEN
        Out.String ("In file ");
        Out.String (source^);
        Out.String (": ");
        Out.Ln;
        lastSource := source
      END;
      IF (source # NIL) THEN
        Out.LongInt (pos, 0);
        Out.String (":")
      END;
      Out.Int (ABS (num), 3);
      Out.Char (" ");
      Out.String (msg);
      Out.Ln
    END WriteError;
  
  BEGIN
    lastSource := NIL;
    err := errList;
    WHILE (err # NIL) DO
      IF includeWarnings OR (err. num > 0) THEN
        WriteError (err. source, err. pos, err. num, err. msg^)
      END;
      err := err. next
    END;
    errList := NIL                       (* remove reference to memory *)
  END EmitErrors;


PROCEDURE ErrIns2* (pos: LONGINT; num: INTEGER; ins1, ins2: ARRAY OF CHAR);
(* Writes error or warning.
   pre: `pos' is valid file position in the current source file (the call is 
     ignored if `pos' is negative), `num' a valid error number (if positive) 
     or warning number (if negative).
   post: The description of `num' is retrieved with `GetErrMsg', if a non-
     empty `ins1' or `ins2' is is inserted into the message with `Replace'.  
     An error is suppressed if it is too close to a previous ones position.
     Otherwise the error/warning is stored in the internal list.  
   NOTE: Use the procedure in `ErrorInstr' when writing error messages in one
   of the optimization or code generation phases! *)
  VAR
    str: ARRAY 256 OF CHAR;
  BEGIN
    IF (pos >= 0) THEN
      IF (num > 0) THEN
        INC (errCount)
      END;
      
      GetErrMsg (ABS (num), str);
      IF (ins1 # "") THEN Replace (str, ins1) END;
      IF (ins2 # "") THEN Replace (str, ins2) END;
      noerr := noerr & (num < 0);
      
      (* collect errors in list, they'll be written (after sorting) to
         stdout by calling `EmitErrors' *)
      StoreError (sourceFile, pos, num, str)
    END
  END ErrIns2;

PROCEDURE ErrIns* (pos: LONGINT; num: INTEGER; ins: ARRAY OF CHAR);
(* NOTE: Use the procedure in `ErrorInstr' when writing error messages in one
   of the optimization or code generation phases! *)
  BEGIN
    ErrIns2 (pos, num, ins, "")
  END ErrIns;

PROCEDURE Err* (pos: LONGINT; num: INTEGER);
(* NOTE: Use the procedure in `ErrorInstr' when writing error messages in one
   of the optimization or code generation phases! *)
  BEGIN
    ErrIns2 (pos, num, "", "")
  END Err;

PROCEDURE ErrOoR* (pos: LONGINT; num: INTEGER; min, maxPlusOne: LONGINT);
(* Generates an "out of range" error message.  The intervall 
   `min <= x < maxPlusOne' is inserted into the error description.
   NOTE: Use the procedure in `ErrorInstr' when writing error messages in one
   of the optimization or code generation phases! *)
  VAR
    range, upper: ARRAY 64 OF CHAR;
  BEGIN
    IntStr.IntToStr (min, range);
    Strings.Append (" <= x < ", range);
    IF (maxPlusOne <= 0) THEN
      Strings.Append ("y", range)
    ELSE
      IntStr.IntToStr (maxPlusOne, upper);
      Strings.Append (upper, range)
    END;
    ErrIns (pos, num, range)
  END ErrOoR;


PROCEDURE FileError* (msg, fileName, error: ARRAY OF CHAR);
  VAR
    str: ARRAY 1024 OF CHAR;
    found: BOOLEAN;
    pos: INTEGER;
  BEGIN
    COPY (msg, str);
    Strings.FindNext ("%", str, 0, found, pos);
    IF found THEN
      Strings.Delete (str, pos, 1);
      Strings.Insert (fileName, pos, str)
    END;
    Out.String ("Error: ");
    Out.String (str);
    Out.Ln;
    Out.String ("       ");
    Out.String (error);
    Out.Ln;
    HALT (1)
  END FileError;

PROCEDURE VerboseMsg* (msg: ARRAY OF CHAR);
(* Writes `msg' plus newline to stdout, unless `verbose. true' is FALSE. *)
  BEGIN
    IF verbose. true THEN
      Out.String (msg);
      Out.Ln;
      Out.Flush
    END
  END VerboseMsg;

PROCEDURE Init*;
(* Has to be called before a compilation is started on a file;  resets the
   error reporting procedures.  *)
  BEGIN
    noerr := TRUE;
    errCount := 0
  END Init;

BEGIN
  errList := NIL;
  errDescrList := NIL;
  errListRead := FALSE;
  sourceFile := NIL;
  
  verbose := Options.CreateBoolean ("verbose", FALSE);
  Options.options. Add (verbose);
  Options.options. CmdLineOption ("-v,--verbose", "verbose:=TRUE");
  
  Pragmas.pragmas. CmdLineOption ("-w,--warnings", "Warnings:=TRUE");
  
  errorMsgs := Options.CreateString ("errorMessages", Config.defaultErrorMsgs);
  Options.options. Add (errorMsgs)
END Error.
