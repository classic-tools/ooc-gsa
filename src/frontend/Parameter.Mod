(* 	$Id: Parameter.Mod,v 1.21 2000/01/09 17:50:57 ooc-devel Exp $	 *)
MODULE Parameter;
(*  Parses configuration files and commmand lines.
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
(* description at the end of this file *)

IMPORT
  Strings, IntStr, Files, ProgramArgs, BinaryRider, TextRider, Filenames,
  Out, Rts;
  
  
CONST
  sizeFilename* = 256;                   
  (* maximum length of file name (incl 0X) *)
  sizeName* = 32;
  (* maximum length of parameter name *)
  maxLevel* = 8;
  (* maximum nesting depth of configuration file includes *)

  (* meta positions that can be passed to Stream.Error *)
  currPos* = -1;                         (* current reading position *)
  currSym* = -2;                         (* position of current token *)

  eol = 0AX;                             (* end of line, ASCII lf *)
  
TYPE
  Filename* = ARRAY sizeFilename OF CHAR;
  (* array that is guaranteed to be able to hold a legal file name (incl. its
     path) on this operating system *)
  String* = POINTER TO ARRAY OF CHAR;
  
  (* the following data type (resp its extensions) hold the information on how
     to parse a configuration file section and how to store the respective
     values found there *)
  Section* = POINTER TO SectionDesc;
  SectionDesc* = RECORD
    next: Section;                         
    (* links list of registered sections in variable `sections' *)
    name-: String;
    (* unique name of section *)
    defined-: BOOLEAN;
    (* TRUE iff a section of this kind occured in a config file (only valid
       after AddSection) *)
    noWrite*: BOOLEAN;
    (* TRUE iff this section should be skipped in WriteConfig; set to FALSE
       by AddSection *)
  END;

  (* a special section that allows to include another file into the current
     configuration file *)
  IncludeSection = POINTER TO IncludeSectionDesc;
  IncludeSectionDesc = RECORD 
    (SectionDesc)
  END;
  
  (* the type CmdLineOption holds information on the registered command line
     options (mostly on the way they have to be interpreted) *)
  CmdLineOption = POINTER TO CmdLineOptionDesc;
  CmdLineOptionDesc = RECORD
    next: CmdLineOption;
    (* links list of options in `cmdList' *)
    section: Section;                    
    (* section that parses this option *)
    cmdNames: String;                    
    (* list of option names, eg "-h,--help" *)
    cmdValue: String;
    (* string that is passed to section.Parse(FALSE) *)
    paramNumber: INTEGER;                
    (* number of following parameters that are copied into `cmdValue' *)
  END;
  LargeString* = ARRAY 2*1024 OF CHAR;
  
  (* the type Stream implements an abstract prototype for an input stream.
     it is used by the sections' parsing procedures *)
  Stream* = POINTER TO StreamDesc;
  StreamDesc = RECORD
    prev: Stream;                        
    (* previous stream in stack (used in connection with IncludeSection) *)
    level: SHORTINT;                     
    (* level in stack *)
    currChar*: CHAR;
    (* current look ahead character, used during parsing *)
    eos-: BOOLEAN;
    (* end of file marker, used during parsing *)
    err-: BOOLEAN;
    (* set to TRUE when Stream.Error is called *)
    currSymPos*: LONGINT;
    (* position of current symbol *)
  END;
  (* FileStream is used to parse configuration files *)
  FileStream* = POINTER TO FileStreamDesc;
  FileStreamDesc = RECORD
    (StreamDesc)
    fileName: Filename;
    (* the name of the file (used for error messages) *)
    f: Files.File;
    r: BinaryRider.Reader
  END;
  (* StringStream is used to parse command line options *)
  StringStream* = POINTER TO StringStreamDesc;
  StringStreamDesc = RECORD
    (StreamDesc)
    s: String;
    (* the input string that is about to being parsed *)
    errorMsg: ARRAY 120 OF CHAR;
    (* first line printed by StringStream.Error *)
    pos: LONGINT;
    (* current reading position in the string `s' *)
  END;


VAR
  sections: Section;
  (* list of registered parameters *)
  cmdList: CmdLineOption;
  (* list of registered command line options *)
  in-: Stream;
  (* stack of stream for configuration statements (file, string, etc) *)
  err: BOOLEAN;
  (* set to TRUE whenever Stream.Error is called *)
  include-: IncludeSection;
  (* the INCLUDE section, can be used as receiver of the procedure
     CmdLineOption *)
  skipArg: INTEGER;
  (* set by ParseConfigFile; if not negative, then the arguments skipArg and
     skipArg+1 should be ignored when parsing the command line (see procedure
     ParseCmdLine) *)
  numArgs: INTEGER;
  (* total number of command line arguments, set by `ParseCmdLine' *)
  restArg: INTEGER;
  (* index of first argument after command line options, set by 
     `ParseCmdLine' *)
  argReader: TextRider.Reader;
  (* program arguments are accessed using this reader *)

PROCEDURE Warning* (msg: ARRAY OF CHAR);
(* Writes "Warning: <msg>" to stdout. *)
  BEGIN
    Out.String ("Warning: ");
    Out.String (msg);
    Out.Ln
  END Warning;

PROCEDURE FatalError* (msg: ARRAY OF CHAR);
(* Writes "Error: <msg>" to stdout and aborts the program. *)
  BEGIN
    Out.String ("Error: ");
    Out.String (msg);
    Out.Ln;
    HALT (1)
  END FatalError;



PROCEDURE IsAlpha* (ch: CHAR): BOOLEAN;
(* Result is TRUE iff `ch' is a character. *)
  BEGIN
    ch := CAP (ch);
    RETURN ("A" <= ch) & (ch <= "Z") OR (ch = "_")
  END IsAlpha;

PROCEDURE IsNum* (ch: CHAR): BOOLEAN;
(* Result is TRUE iff `ch' is a decimal cypher. *)
  BEGIN
    RETURN ("0" <= ch) & (ch <= "9")
  END IsNum;




(* 
The following type-bound procedures provide an abstract interface for the
Stream data type.  They provide functionality to 
 - install or remove a stream
 - parse a stream one character at a time
 - skip whitespace characters
 - read an identifier, string, or name
 - match the current symbol to a given string
 - inquire about the current reading position
 - emit an error message.
For concrete implementations take a look a FileStream and StringStream below.
*)

PROCEDURE (s: Stream) Remove*;
(* Removes the stream `s' from the stream stack.
   pre: `s' is the current top of stack, ie `s=in' *)
  BEGIN
    ASSERT (s = in);
    in := s. prev
  END Remove;

PROCEDURE (s: Stream) NextChar*;
(* Read current character in input stream, ie transfer character at s.CurrPos()
   into `s. currChar' and advance the reading position by 1.  If the current
   position is behind the last character, ie when no further character can be
   read, set `s. eos' to TRUE.  Additionally the stream `s' will be removed 
   from the stack (unless it's the last one) and `s. currChar' will be set to 
   0X if `s. eos' is set. *)
  BEGIN
    IF s. eos THEN
      IF (s. prev # NIL) THEN     (* remove stacked stream *)
        s. Remove
      END;
      s. currChar := 0X
    END
  END NextChar;

PROCEDURE (s: Stream) Install*;
(* Installs `s' as current input stream on the stack `in', initializes it
   and calls `s. NextChar' to read the first character. *)
  BEGIN
    s. prev := in;
    IF (in # NIL) THEN
      s. level := in. level+1;
      IF (s. level >= maxLevel) THEN
        FatalError ("Configuration nesting exceeds limit")  (* vague, agreed *)
      END
    ELSE
      s. level := 0
    END;
    s. eos := FALSE;
    s. err := FALSE;
    in := s;
    (* initialize character stream *)
    in. NextChar
  END Install;
  
PROCEDURE (s: Stream) Error* (pos: LONGINT; msg: ARRAY OF CHAR);
(* Writes error message `msg' with regard to stream position `pos'.  For 
   `pos=currPos' the current position in the stream is used for the error
   position, for `pos=currSym' the position of the current symbol. 
   The variables `s.err', `s.eos', `err' will be set to TRUE, `s.currChar'
   to 0X, or the program can be aborted.  *)
  BEGIN
    s. err := TRUE;
    s. eos := TRUE;
    s. currChar := 0X;
    err := TRUE
  END Error;

PROCEDURE (s: Stream) CurrPos*(): LONGINT;
(* Result is the current reading position in stream `s', ie the position of
   the character in `currChar', or -1 if no character has been read yet. *)
  END CurrPos;

PROCEDURE (s: Stream) SkipWhitespace*;
(* Skips whitespace characters, ie characters with ASCII below/equal to " " and
   any comments (started with "#"). *)
  BEGIN
    REPEAT
      WHILE ~s. eos & (s. currChar <= " ") DO
        s. NextChar
      END;
      IF (s. currChar = "#") THEN        (* skip comment *)
        WHILE ~s. eos & (s. currChar # eol) DO
          s. NextChar
        END
      END
    UNTIL s. eos OR ((s. currChar > " ") & (s. currChar # "#"));
    
    IF (in # s) THEN
      (* the end of input stream `s' was reached and we switched back into 
         another stream; note that `in' is never set to NIL *)
      in. SkipWhitespace
    END
  END SkipWhitespace;

PROCEDURE (s: Stream) ReadIdent* (VAR ident: ARRAY OF CHAR);
(* Reads identifier from stream `s'.  Any leading whitespace is skipped.  An
   error is printed if the following symbol is no identifier or if it is too 
   long to fit into `ident'.  The position of the symbol is stored in 
   `s. currSymPos'. 
   Regular expression for identifiers: [a-zA-Z][a-zA-Z0-9]* *)
  VAR
    i: LONGINT;
  BEGIN
    s. SkipWhitespace;
    s. currSymPos := s. CurrPos();
    IF ~s. eos & IsAlpha (s. currChar) THEN
      (* read characters til the first non alphanumeric char *)
      i := 0;
      WHILE IsAlpha (s. currChar) OR IsNum (s. currChar) DO
        IF (i < LEN (ident)) THEN
          ident[i] := s. currChar
        END;
        INC (i);
        s. NextChar
      END;
      (* terminate string if possible, otherwise emit error *)
      IF (i < LEN (ident)) THEN
        ident[i] := 0X
      ELSE
        s. Error (s. currSymPos, "Identifier too long");
        ident[LEN (ident)-1] := 0X
      END
    ELSE
      s. Error (currSym, "Identifier expected")
    END
  END ReadIdent;

PROCEDURE (s: Stream) ReadInteger* (VAR num: ARRAY OF CHAR);
(* Reads integer from stream `s'.  Any leading whitespace is skipped.  An
   error is printed if the following symbol is no integer or if it is too 
   long to fit into `num'.  The position of the symbol is stored in 
   `s. currSymPos'. 
   Regular expression for integers: [+-][0-9][0-9]* *)
  VAR
    i: LONGINT;
  BEGIN
    s. SkipWhitespace;
    s. currSymPos := s. CurrPos();
    IF ~s. eos & 
       (IsNum (s. currChar) OR (s. currChar = "-") OR (s. currChar = "+")) THEN
      (* read characters til the first non numeric char *)
      i := 0;
      REPEAT
        IF (i < LEN (num)) THEN
          num[i] := s. currChar
        END;
        INC (i);
        s. NextChar
      UNTIL ~IsNum (s. currChar);
      
      (* terminate string if possible, otherwise emit error *)
      IF (i < LEN (num)) THEN
        num[i] := 0X
      ELSE
        s. Error (s. currSymPos, "Integer too long");
        num[LEN (num)-1] := 0X
      END
    ELSE
      s. Error (currSym, "Integer expected")
    END
  END ReadInteger;

PROCEDURE (s: Stream) ReadString* (VAR str: ARRAY OF CHAR);
(* Reads string from stream `s'.  A string has the form ".." or '..', where ..
   stands for an arbitrary number of characters with ASCII code greater/equal
   to " ".  An error is printed if the following symbol is no string or if it 
   is too long to fit into `str'.  
   Leading whitespace characters are skipped.  The position of the symbol is 
   stored in `s. currSymPos'. *)
  VAR
    i: LONGINT;
    end: CHAR;
  BEGIN
    s. SkipWhitespace;
    s. currSymPos := s. CurrPos();
    end := s. currChar;
    IF (end # "'") & (end # '"') THEN    (* string delimiter: " or ' *)
      s. Error (currSym, "String expected")
    ELSE
      s. NextChar;
      (* collect characters til matching trailing delimiter *)
      i := 0;
      WHILE (s. currChar >= " ") & (s. currChar # end) DO
        IF (i < LEN (str)) THEN
          str[i] := s. currChar
        END;
        INC (i);
        s. NextChar
      END;
      IF (s. currChar < " ") THEN
        s. Error (s. currSymPos, "Illegal code in string, or string not terminated")
      ELSE
        s. NextChar;                     (* skip trailing delimiter *)
        IF (i >= LEN (str)) THEN
          s. Error (s. currSymPos, "String too long");
          str[LEN (str)-1] := 0X
        ELSE
          str[i] := 0X
        END
      END
    END
  END ReadString;

PROCEDURE (s: Stream) ReadName* (sep: ARRAY OF CHAR; VAR name: ARRAY OF CHAR);
(* Reads name from stream `s'.  A name is an arbitrary number of characters 
   with ASCII code greater than " " (but not "#") that are not part of `sep'.  
   An error is printed if the following symbol is no name or if it is too long
   to fit into `name'.  
   Leading whitespace characters are skipped.  The position of the symbol is 
   stored in `s. currSymPos'. *)
  VAR
    i: LONGINT;
  
  PROCEDURE IsSep(): BOOLEAN;
  (* Result is TRUE if `s. currChar' occurs in `sep'. *)
    VAR
      i: INTEGER;
    BEGIN
      i := 0;
      WHILE (sep[i] # 0X) & (sep[i] # s. currChar) DO
        INC (i)
      END;
      RETURN (sep[i] # 0X)
    END IsSep;
    
  BEGIN
    s. SkipWhitespace;
    IF s. eos OR IsSep() THEN
      s. Error (currSym, "Name expected")
    ELSE
      s. currSymPos := s. CurrPos();
      (* read characters til the first whitespace or `sep' char *)
      i := 0;
      REPEAT
        IF (i < LEN (name)) THEN
          name[i] := s. currChar
        END;
        INC (i);
        s. NextChar
      UNTIL IsSep() OR (s. currChar <= " ") OR (s. currChar = "#");
      (* terminate string if possible, otherwise emit error *)
      IF (i < LEN (name)) THEN
        name[i] := 0X
      ELSE
        s. Error (currSym, "Name too long");
        name[LEN (name)-1] := 0X
      END
    END
  END ReadName;

PROCEDURE (s: Stream) LookingAtString* (VAR str: ARRAY OF CHAR): BOOLEAN;
(* If, after skipping all whitespace characters, the current character is a
   string delimiter, then read this string into `str' and return TRUE.  
   Otherwise do nothing and return FALSE.  Used whenever a symbol can be a
   string (if quoted) or something else (eg a name) if unquoted. *)
  BEGIN
    s. SkipWhitespace;
    IF (s. currChar = "'") OR (s. currChar = '"') THEN  (* got " or '? *)
      s. ReadString (str);
      RETURN TRUE
    ELSE
      RETURN FALSE
    END
  END LookingAtString;

PROCEDURE (s: Stream) Match* (sym: ARRAY OF CHAR);
(* Skips whitespace and compares the following symbol with `sym'.  If `sym'
   starts with a character (eg `sym="END"'), then s.ReadIdent is called and
   the result compared with `sym', otherwise the following characters are 
   compare with `sym' on a per character basis.  On mismatch an error is
   printed. *)
  VAR
    ident: Filename;
    i: INTEGER;
    err: BOOLEAN;
  BEGIN
    err := FALSE;
    s. SkipWhitespace;
    s. currSymPos := s. CurrPos();
    IF IsAlpha (sym[0]) THEN             (* `sym' is an identifier *)
      IF s. eos OR ~IsAlpha (s. currChar) THEN
        err := TRUE
      ELSE
        s. ReadIdent (ident);
        err := (ident # sym)
      END
    ELSE                                 (* compare per character with `sym' *)
      i := 0;
      WHILE (sym[i] # 0X) & (s. currChar = sym[i]) DO
        s. NextChar;
        INC (i)
      END;
      err := (sym[i] # 0X)
    END;
    IF err THEN                          (* mismatch found, print error *)
      COPY (sym, ident);
      Strings.Append (" expected", ident);
      s. Error (currSym, ident)
    END
  END Match;



(* 
The following procedures provide an abstract interface for the Section data 
type.  They provide functionality to 
 - register a section
 - find a section, given its name
 - parse a section 
 - write the contents of a section 
A section is (in general) a set of attribute+name pairs that are set by a
configuration file or command line options.
For concrete implementations take a look a ParamOptions.OptionsSection or
ParamFiles.FilesSection.
*)

PROCEDURE GetSection* (name: ARRAY OF CHAR): Section;
(* Return the section named `name', or NIL if no such thing exists. *)
  VAR
    s: Section;
  BEGIN
    s := sections;
    WHILE (s # NIL) & (s. name^ # name) DO
      s := s. next
    END;
    RETURN s
  END GetSection;
  
PROCEDURE AddSection* (name: ARRAY OF CHAR; s: Section);
(* Register section under the name `name'.  
   pre: No section of the same name is registered already. *)
  VAR
    s0: Section;
  BEGIN
    ASSERT (GetSection (name) = NIL);
    s. next := NIL;
    NEW (s. name, Strings.Length (name)+1);
    COPY (name, s. name^);
    s. defined := FALSE;
    s. noWrite := FALSE;
    (* add section to end of list *)
    s0 := sections;
    IF (s0 = NIL) THEN
      sections := s
    ELSE
      WHILE (s0. next # NIL) DO
        s0 := s0. next
      END;
      s0. next := s
    END
  END AddSection;

PROCEDURE (section: Section) Parse* (includeEnd: BOOLEAN);
(* Parses contents of a section from the input stream `in'.  
   If `includeEnd=TRUE', expect the keyword END to terminate the section (and 
   stop parsing with this word; it is assumed that the first occurence of the
   identifier END ends the section), otherwise parse until `in.eos=TRUE' (in 
   which case END has no special meaning). *)
  BEGIN
    IF includeEnd THEN                   (* check for end of section *)
      in. Match ("END")
    END
  END Parse;

PROCEDURE (section: Section) Write*; 
(* Writes contents of section. *)
  END Write;

PROCEDURE ParseInteger (VAR str: ARRAY OF CHAR; VAR pos: INTEGER): INTEGER;
(* Parse a symbol in of the form "$[0-9]+" in `str', starting at `pos'.  If the
   symbol contains a valid number (ie, has the correct syntax and fits into an
   INTEGER), `pos' is advanced behind the symbol and the number is returned.
   Otherwise `pos' is only incremented behind the "$" and the result is -1. 
   pre: str[pos]="$" *)
  VAR
    i: INTEGER;
    num: LONGINT;
    numStr: ARRAY 16 OF CHAR;
    format: IntStr.ConvResults;
  BEGIN
    INC (pos);
    (* skip digits *)
    i := pos;
    WHILE IsNum (str[i]) DO 
      INC (i)
    END;
    IF (i # pos) THEN  (* non-empty sequence of digits found *)
      Strings.Extract (str, pos, i-pos, numStr);
      IntStr.StrToInt (numStr, num, format);
      IF (format = IntStr.strAllRight) & (num < MAX (INTEGER)) THEN
        pos := i;
        RETURN SHORT (num)
      ELSE                               (* conversion error or too large *)
        RETURN -1
      END
    ELSE                                 (* no digits found *)
      RETURN -1
    END
  END ParseInteger;

PROCEDURE (s: Section) CmdLineOption* (cmdNames, cmdValue: ARRAY OF CHAR);
(* Register command line option(s) for the section `s'.  `cmdNames' is a list
   of names for the option seperated by ",", eg cmdNames="-f,--flags".  
   `cmdValues' is the string that is evaluated (passed to s.Parse(FALSE)) when
   such an option is found, eg cmdValue="flags=$1".  If the value contains
   $1, $2, etc then those wildcards are replaced by the first, second, etc
   argument following the initial option name. *)
  VAR
    i, num: INTEGER;
    cmd: CmdLineOption;
  BEGIN
    NEW (cmd);
    cmd. section := s;
    cmd. paramNumber := 0;
    (* find out how many parameters follow this one on the command line *)
    i := 0;
    WHILE (cmdValue[i] # 0X) DO
      IF (cmdValue[i] = "$") THEN
        num := ParseInteger (cmdValue, i);
        IF (num > cmd. paramNumber) THEN
          cmd. paramNumber := num
        END
      ELSE
        INC (i)
      END
    END;
    (* store name and value *)
    NEW (cmd. cmdNames, Strings.Length (cmdNames)+1);
    COPY (cmdNames, cmd. cmdNames^);
    NEW (cmd. cmdValue, Strings.Length (cmdValue)+1);
    COPY (cmdValue, cmd. cmdValue^);
    (* add command to list *)
    cmd. next := cmdList;
    cmdList := cmd
  END CmdLineOption;

PROCEDURE SkipSection;
(* Skip current section, ie until the keyword END is found. *)
  VAR
    i: INTEGER;
    ident: ARRAY 4 OF CHAR;
    delim: CHAR;
  BEGIN  (* unknown section: skip text til first END *)
    LOOP
      in. SkipWhitespace;
      IF in. eos THEN  (* blast, no END found *)
        in. Error (currPos, "END expected");
        EXIT
      ELSIF (in. currChar = '"') OR (in. currChar = "'") THEN
        (* skip strings starting with " or ' *)
        delim := in. currChar;
        in. NextChar;
        WHILE ~in. eos & (in. currChar # delim) & (in. currChar >= " ") DO
          in. NextChar
        END;
        in. NextChar
      ELSIF IsAlpha (in. currChar) THEN  
        (* check for END: read identifier (truncate after 3 chars) *)
        i := 0;
        WHILE IsAlpha (in. currChar) OR IsNum (in. currChar) DO
          IF (i < LEN (ident)) THEN
            ident[i] := in. currChar
          END;
          INC (i);
          in. NextChar
        END;
        (* test for keyword END *)
        IF (i = 3) THEN
          ident[i] := 0X;
          IF (ident = "END") THEN
            EXIT
          END
        END
      ELSE
        WHILE (in. currChar > " ") &
              ~(IsAlpha (in. currChar) OR (in. currChar = "#") OR
                (in. currChar = "'") OR (in. currChar = '"')) DO
          (* loop over contiguos segment of characters until an alphanumeric, 
             a whitespace character, a comment, or one of the string 
             delimiters ' or " is found *)
          in. NextChar
        END
      END
    END
  END SkipSection;





(*
The following procedures parse the configuration file.  For that purpose an 
abstract data type `FileStream' is created as an extension of `Stream'.  A 
special section `Include' is defined.  Finally the procedure ParseConfigFile 
is implemented to read and interpret a configuration file. 
*)

PROCEDURE (s: FileStream) Install*;
(* Installs `s' as current input stream on the stack `in', initializes it
   and calls `s. NextChar' to read the first character. 
   pre: the file `s. f' must have been opened successfully.  *)
  BEGIN
    s. r := BinaryRider.ConnectReader (s. f);
    s. Install^
  END Install;

PROCEDURE (s: FileStream) Remove*;
(* Closes the file `s. f' and removes the stream `s' from the stream stack.
   pre: `s' is the current top of stack, ie `s=in' *)
  BEGIN
    s. f. Close;
    s. Remove^
  END Remove;

PROCEDURE (s: FileStream) NextChar*;
(* Read current character in input stream, ie transfer character at s.CurrPos()
   into `s. currChar' and advance the reading position by 1.  If the current
   position is behind the last character, ie when no further character can be
   read, set `s. eos' to TRUE.  Additionally the stream `s' will be removed 
   from the stack (unless it's the last one) and `s. currChar' will be set to 
   0X, if `s. eos' is set. *)
  BEGIN
    IF ~s. eos THEN
      s. r. ReadChar (s. currChar);
      s. eos := (s. r. res # Files.done) &
                (s. r. res. code = Files.readAfterEnd);
      IF ~s. eos & (s. r. res # Files.done) THEN
        s. Error (currPos, "Read error")
      END;
      s. NextChar^  (* removes `s' from stack if necessary *)
    END
  END NextChar;

PROCEDURE (s: FileStream) Error* (pos: LONGINT; msg: ARRAY OF CHAR);
(* Writes error message `msg' with regard to the file assciated to `s' and 
   stream position `pos'.  For `pos=currPos' the current position in the file
   is used for the error position, for `pos=currSym' the position of the 
   current symbol. 
   Finally the program is aborted. *)
  BEGIN
    IF (pos = currPos) THEN
      pos := s. CurrPos()
    ELSIF (pos = currSym) THEN
      pos := s. currSymPos
    END;
    s. Error^ (pos, msg);
    Out.String ("Error in ");
    Out.String (s. fileName);
    Out.String (" at pos ");
    Out.LongInt (pos, 0);
    Out.Char (":");
    Out.Ln;
    Out.String (msg);
    Out.Ln;
    HALT (1)
  END Error;

PROCEDURE (s: FileStream) CurrPos*(): LONGINT;
(* Result is the current reading position of the rider `s. r', ie the position
   of the character in `currChar', or -1 if no character has been read yet. *)
  BEGIN
    RETURN s. r. Pos()-1
  END CurrPos;


PROCEDURE GetIndexedArg (index: INTEGER; VAR arg: ARRAY OF CHAR);
  BEGIN
    argReader. SetPos (0);
    WHILE (index > 0) DO
      argReader. ReadLn;
      DEC (index)
    END;
    argReader. ReadLine (arg)
  END GetIndexedArg;


PROCEDURE ParseConfigFile* (configFile, envVar, configOveride: ARRAY OF CHAR;
                            enableInclude, skipUnknownSection: BOOLEAN;
                            VAR fileParsed: ARRAY OF CHAR);
(* Parse the configuration file `configFile' (or the value of an environment
   variable `envVar', if it exists) and print a warning if it can't be opened.
   If `configOveride' is a non-empty string and one command line argument 
   equals `configOveride', use the following argument for the name of the 
   configuration file.  This option must be part of the command's option list
   and cannot be placed amongst the non option arguments.  If the name of the
   configuration file is somehow set to the empty string no configuration file
   will be parsed at all.  This allows to suppress reading a config file as a
   command line option.  The flag `enableInclude' allows the use the special 
   INCLUDE section in the config file.  If `skipUnknownSection=TRUE', sections
   whose name aren't registered are skipped (ie, the input stream is discarded
   until an END is found), otherwise an error is generated and the program 
   halted. 
   In `fileParsed' the name of the actually used top-level configuration file
   is returned.  *)
  VAR
    fileStream: FileStream;
    str: Filename;
    ident: ARRAY 32 OF CHAR;
    section: Section;
    arg: INTEGER;
    res: Files.Result;
    
  PROCEDURE ConfigFileOption (configOveride: ARRAY OF CHAR): INTEGER;
  (* Scan the command line for an argument `configOveride'.  If one is present,
     take the following argument as name of the configuration file.  Arguments
     after "--" are ignored.  *)
    VAR
      argName: Filename;
      arg: INTEGER;
    BEGIN
      IF (configOveride # "") THEN
        arg := 1;
        WHILE (arg <= ProgramArgs.args. ArgNumber()) DO
          GetIndexedArg (arg, argName);
          IF (argName = "--") THEN
            RETURN -1
          ELSIF (argName = configOveride) THEN
            IF (ProgramArgs.args. ArgNumber() > arg) THEN
              RETURN arg+1
            ELSE  (* `Param.in' isn't initialized, use FatalError instead *)
              argName := "Missing file name after ";
              Strings.Append (configOveride, argName);
              FatalError (argName)
            END
          ELSE
            INC (arg)
          END
        END
      END;
      RETURN -1
    END ConfigFileOption;
  
  BEGIN
    (* create basic file stream *)
    NEW (fileStream);
    
    (* overide file parameter if an environment variable or a command line 
       option specifies another file name *)
    IF (envVar = "") OR ~Rts.GetEnv (fileStream. fileName, envVar) THEN
      (* if no environment variable defines the path, use the default *)
      COPY (configFile, fileStream. fileName)
    END;
    arg := ConfigFileOption (configOveride);
    IF (arg >= 0) THEN  (* file path set by explicit option *)
      GetIndexedArg (arg, fileStream. fileName);
      skipArg := arg-1
    ELSE
      skipArg := -1
    END;
    
    (* register IncludeSection if `enableInclude' is set *)
    IF enableInclude THEN
      AddSection ("INCLUDE", include);
      include. noWrite := TRUE
    END;
    COPY (fileStream. fileName, fileParsed);
    
    IF (fileStream. fileName # "") THEN
      (* open main configuration file *)
      Filenames.ExpandPath (fileStream. fileName, fileStream. fileName);
      fileStream. f := Files.Old (fileStream. fileName, {Files.read}, res);
      IF (fileStream. f = NIL) THEN        (* no file: warning and exit *)
        str := "Can't open config file ";
        Strings.Append (fileStream. fileName, str);
        Warning (str)
      ELSE
        fileStream. Install;
        in. SkipWhitespace;
        WHILE ~in. eos DO
          in. ReadIdent (ident);           (* read section name *)
          IF ~in. err THEN
            section := GetSection (ident); (* find section data *)
            IF (section = NIL) THEN        (* unknown section: skip it *)
              IF skipUnknownSection THEN
                SkipSection
              ELSE
                str := "Unknown section ";
                Strings.Append (ident, str);
                in. Error (currSym, str);
                HALT (1)
              END
            ELSE
              section. defined := TRUE;
              section. Parse (TRUE)        (* parse section (with END) *)
            END
          END;
          in. SkipWhitespace
        END;
        IF (in = fileStream) THEN
          in. Remove                       (* clear stack *)
        END
      END
    END
  END ParseConfigFile;

PROCEDURE (incl: IncludeSection) Parse* (includeEnd: BOOLEAN);
(* Parses the contents of the special INCLUDE section from the input stream 
   `in'.  A file name is read and a new stream for this file is placed at the
   top of the input stack.  Nothing is done (and no warning given) if the file
   can't be opened.  The new file stream is removed when Stream.NextChar 
   reaches the end of the stream.
   If `includeEnd=TRUE', expect the keyword END to terminate the section (and 
   stop parsing with this word; it is assumed that the first occurence of the
   identifier END ends the section), otherwise parse until `in.eos=TRUE' (in 
   which case END has no special meaning). *)
  VAR
    fileStream: FileStream;
    res: Files.Result;
    dummy: ARRAY 2 OF CHAR;
  BEGIN
    NEW (fileStream);
    IF ~in. LookingAtString (fileStream. fileName) THEN
      in. ReadName ("", fileStream. fileName)
    END;
    incl. Parse^ (includeEnd);           (* parse behind END *)
    IF includeEnd THEN                   (* called from ParseConfigFile *)
      (* try to open the file, abort silently on failure *)
      Filenames.ExpandPath (fileStream. fileName, fileStream. fileName);
      fileStream. f := Files.Old (fileStream. fileName, {Files.read}, res);
      IF (fileStream. f # NIL) THEN
        fileStream. Install              (* will be removed on eos *)
      END
    ELSE                                 (* called from ParseCmdLine *)
      ParseConfigFile (fileStream. fileName, "", "", FALSE, FALSE, dummy)
    END
  END Parse;

PROCEDURE WriteConfig*;
(* Writes current contents of all registered sections that haven't set the
   flag `noWrite'. *)
  VAR
    s: Section;
  BEGIN
    s := sections;
    WHILE (s # NIL) DO
      IF ~s. noWrite THEN
        Out.String (s. name^);
        Out.Ln;
        s. Write;
        Out.String ("END");
        Out.Ln
      END;
      s := s. next
    END
  END WriteConfig;



(*
The following procedures handle the parsing of the command line arguments.  For
that purpose an abstract data type `StringStream' is created as an extension of
`Stream'.  It is used to to parse the "mini" sections into which each command
line option is converted by using the translation pattern passed with
Section.CmdLineOption.  The procedure ParseCmdLine reads and interpret the 
options, the remaining arguments can be read with GetArg. 
*)

PROCEDURE (s: StringStream) Install*;
(* Installs `s' as current input stream on the stack `in', initializes it
   and calls `s. NextChar' to read the first character. 
   pre: the string `s. s' must have been initialized beforehand.  *)
  BEGIN
    s. pos := 0;
    s. Install^
  END Install;

PROCEDURE (s: StringStream) NextChar*;
(* Read current character in input stream, ie transfer character at s.CurrPos()
   into `s. currChar' and advance the reading position by 1.  If the current
   position is behind the last character, ie when no further character can be
   read, set `s. eos' to TRUE.  Additionally the stream `s' will be removed 
   from the stack (unless it's the last one) and `s. currChar' will be set to 
   0X, if `s. eos' is set. *)
  BEGIN
    IF ~s. eos THEN
      IF (s. s[s. pos] = 0X) THEN
        s. eos := TRUE
      ELSE
        s. currChar := s. s[s. pos];
        INC (s. pos)
      END;
      s. NextChar^
    END
  END NextChar;

PROCEDURE (s: StringStream) Error* (pos: LONGINT; msg: ARRAY OF CHAR);
(* Writes error message `msg' with regard to the string in  `s. s' and stream 
   position `pos'.  For `pos=currPos' the current position in the file
   is used for the error position, for `pos=currSym' the position of the 
   current symbol.  The first line written is the value of `s. errorMsg' 
   (unless it's empty).
   Finally the program is aborted. *)
  VAR
    i: LONGINT;
  BEGIN
    IF (pos = currPos) THEN
      pos := s. CurrPos()
    ELSIF (pos = currSym) THEN
      pos := s. currSymPos
    END;
    s. Error^ (pos, msg);
    IF (s. errorMsg # "") THEN           (* non-empty first line? *)
      Out.String (s. errorMsg);
      Out.Ln
    END;
    Out.String (s. s^);
    Out.Ln;
    (* mark error position and write error message *)
    FOR i := 0 TO pos-1 DO
      Out.Char ("-")
    END;
    Out.String ("^  ");
    Out.String (msg);
    Out.Ln;
    HALT (1)
  END Error;

PROCEDURE (s: StringStream) CurrPos*(): LONGINT;
(* Result is the current reading position in stream `s', ie the position of
   the character in `currChar', or -1 if no character has been read yet. *)
  BEGIN
    RETURN s. pos-1
  END CurrPos;


PROCEDURE ParseCmdLine* (optionsStartWithDash, multSingleChar, enableDashDash: BOOLEAN): INTEGER;
(* Parse command line and evaluate options.
     optionsStartWithDash: If TRUE, consider each argument found in a potential
       option position as an option if it starts with `-'.  Otherwise consider
       it as an additional parameter following the option list and don't write
       an error message (and abort the parsing of the options at this place).
     multSingleChar: If TRUE and an argument has the form "-XYZ" (where X can 
       be any character execept "-"), and it doesn't match any registered 
       option, try to interpret it like the argument list "-X -Y -Z".
     enableDashDash: If TRUE, then "--" can be used to mark the end of the
       option list.  
   result: Number of arguments following the last option. *)
  CONST
    cmdSepChar = ",";
  VAR
    i, j: INTEGER;
    currArg, msg: LargeString;
    cmd: CmdLineOption;
    strStream: StringStream;
    
  PROCEDURE FindCmd (cmdName: ARRAY OF CHAR): CmdLineOption;
  (* Find registered command matching the name `cmdName', return NIL if none
     is found. *)
    VAR
      cmd: CmdLineOption;
      i, len, pos: INTEGER;
      found: BOOLEAN;
    BEGIN
      (* make sure that `cmdName' doesn't contain the seperation char *)
      i := 0;
      WHILE (cmdName[i] # 0X) DO
        IF (cmdName[i] = cmdSepChar) THEN
          RETURN NIL
        ELSE
          INC (i)
        END
      END;
      (* search for `cmdName' in the registered command line options *)
      len := Strings.Length (cmdName);
      cmd := cmdList;
      i := 0;
      WHILE (cmd # NIL) DO
        Strings.FindNext (cmdName, cmd. cmdNames^, 0, found, pos);
        WHILE found DO
          IF ((pos = 0) OR (cmd. cmdNames[pos-1] = cmdSepChar)) &
             ((cmd. cmdNames[pos+len] = 0X) OR 
              (cmd. cmdNames[pos+len] = cmdSepChar)) THEN
            (* pattern found, and the pattern stretches over the full command
               line option (limited by `cmdSepChar' or end of string) *)
            RETURN cmd
          ELSE
            INC (pos)
          END;
          Strings.FindNext (cmdName, cmd. cmdNames^, pos, found, pos)
        END;
        cmd := cmd. next
      END;
      RETURN NIL
    END FindCmd;
  
  PROCEDURE EvalOption (VAR optName: ARRAY OF CHAR; cmd: CmdLineOption; VAR optIndex: INTEGER);
  (* Evaluate option, ie get the value assciated with the command `cmd', fill 
     in any wildcards, initialize a StringStream with the result, and pass it
     to in.Parse(FALSE).  The value `optIndex' is incremented by the number of
     the additional arguments used (ie, stays as it is if no argument is 
     used). *)
    VAR
      str, param: LargeString;
      numStr: ARRAY 32 OF CHAR;
      num, i, pos: INTEGER;
    BEGIN
      IF (optIndex+cmd. paramNumber > numArgs) THEN
        str := "Option ";
        Strings.Append (optName, str);
        Strings.Append (" expects ", str);
        IF (cmd. paramNumber = 1) THEN
          Strings.Append ("a parameter", str)
        ELSE
          IntStr.IntToStr (cmd. paramNumber, numStr);
          Strings.Append (numStr, str);
          Strings.Append (" parameters", str)
        END;
        FatalError (str)
      ELSE
        COPY (cmd. cmdValue^, str);
        IF (cmd. paramNumber # 0) THEN
          (* insert additional parameters into value string *)
          i := 0;
          WHILE (str[i] # 0X) DO
            IF (str[i] = "$") THEN  
              (* check that are we looking at a place for a parameter *)
              pos := i;
              num := ParseInteger (str, i);
              IF (num > 0) THEN          (* insert parameter here *)
                Strings.Delete (str, pos, i-pos);
                GetIndexedArg (optIndex+num, param);
                Strings.Insert (param, pos, str);
                INC (i, Strings.Length (param)-(pos-i))
              END
            ELSE
              INC (i)
            END
          END;
          INC (optIndex, cmd. paramNumber)
        END;
        (* evaluate string `str' *)
        i := Strings.Length (str);
        IF (i > LEN (strStream. s^)) THEN
          NEW (strStream. s, i+256)
        END;
        COPY (str, strStream. s^);
        strStream. Install;
        cmd. section. Parse (FALSE);
        strStream. Remove
      END
    END EvalOption;
  
  BEGIN
    (* prepare `strStream' for procedure `EvalOptions' *)
    NEW (strStream);
    NEW (strStream. s, 256);
    strStream. errorMsg := "Error while evaluating command line option:";
    
    (* parse arguments *)
    numArgs := SHORT (ProgramArgs.args. ArgNumber());
    restArg := -2;
    
    (* start reading arguments at index 1, unless the first two arguments are
       skipped  *)
    IF (skipArg = 1) THEN
      i := 3
    ELSE
      i := 1
    END;
    WHILE (i <= numArgs) & (restArg < 0) DO
      GetIndexedArg (i, currArg);
      
      (* first try to find a perfect match with one command line option *)
      cmd := FindCmd (currArg);
      IF (cmd # NIL) THEN
        EvalOption (currArg, cmd, i)
      ELSIF enableDashDash & (currArg = "--") THEN  (* end of options *)
        restArg := i+1
      ELSIF multSingleChar & (currArg[0] = "-") & (currArg[1] # "-") THEN
        (* interpret argument as multiple single character options without 
           any following parameters *)
        msg := "-?";
        j := 1;
        WHILE (currArg[j] # 0X) DO
          msg[1] := currArg[j];
          cmd := FindCmd (msg);
          IF (cmd = NIL) THEN
            Strings.Insert ("Unknown option ", 0, msg);
            FatalError (msg)
          ELSIF (cmd. paramNumber # 0) THEN
            Strings.Insert ("Option ", 0, msg);
            Strings.Append (" expects parameter(s) and must stand for its own", msg);
            FatalError (msg)
          ELSE
            EvalOption (msg, cmd, i)
          END;
          INC (j)
        END
      ELSIF optionsStartWithDash & (currArg[0] = "-") THEN
        msg := "Unknown option ";
        Strings.Append (currArg, msg);
        FatalError (msg)
      ELSE  (* unknown option: probably end of list *)
        restArg := i
      END;
      INC (i);
      IF (i = skipArg) THEN
        INC (i, 2)
      END
    END;
    
    IF (restArg = skipArg) THEN
      INC (restArg, 2)
    ELSIF (skipArg > restArg) & (restArg >= 0)THEN
      (* name of configuation file is specified somewhere in the programs 
         additional (non option) arguments *)
      FatalError ("Configuration file overide must be part of option list")
    END;
    
    (* all options parsed *)
    IF (restArg < 0) THEN  (* nothing follows after last option *)
      RETURN 0
    ELSE
      RETURN numArgs-restArg+1
    END
  END ParseCmdLine;

PROCEDURE GetArg* (index: INTEGER; VAR arg: ARRAY OF CHAR);
(* pre: `ParseCmdLine' has been run and 0 <= index < result(ParseCmdLine) *)
  BEGIN
    GetIndexedArg (restArg+index, arg)
  END GetArg;


BEGIN
  sections := NIL;
  cmdList := NIL;
  in := NIL;
  NEW (include);
  include. defined := FALSE;
  include. noWrite := TRUE;
  argReader := TextRider.ConnectReader (ProgramArgs.args)
END Parameter.



(*
This module provides the basic facilities for handling configuration files and
for interpreting of command line arguments.  

A configuration file has the form
	SECTION1
	  ...
	END
	SECTION2
	  ...
	END
It is seperated into several sections whose contents are parsed by dedicated 
modules.  Example: The module `ParamOptions' provides the OPTIONS section, 
where an option is a (name, value) pair whose value can be a boolean, an 
integer, or a string.  An options section could look like this:
	OPTIONS
          warnings := FALSE
          limitLength := 23
        END
A new section (like OPTIONS or PATHS) is added by extending the type 
`Parameter.Section', redefining the procedure `Parse', and registering the
section by calling `Parameter.AddSection'.  The parsing procedure must read
a token stream from `Parameter.in' through the procedures bound to this 
variable.  See the prototype `Parameter.Section.Parse' and the implementations
`ParamOptions' and `ParamPaths' for details.

The special section INCLUDE is defined in `Parameters'.  It expects a file name
as parameter and includes this file into the current input stream.  
Example:
	INCLUDE ~/.myconfig END
        
After registering all sections, the configuration file is parsed by calling
  PROCEDURE ParseConfigFile (configFile, envVar, configOveride: ARRAY OF CHAR; 
                             enableInclude, skipUnknownSection: BOOLEAN);
This procedure is defined in `Parameters'.  Its parameters mean
`configFile'
  The name of the configuration file that will be parsed.
`envVar'
  The name of an environment variable, or the empty string.  If a variable of
  the given name exists, its contents supersede the value of `configFile'.
`configOveride'
  If you want to allow the user to read her own file without parsing 
  `configFile' at all, you can provide the name of a command line option here
  that allows to specify a different file.  Note: When invoking the program, 
  this option must be the first in the line, otherwise it'll be treated like
  any other option (and will probably an `unknown option' error).
  Example:  
    The program `foo' calls ParseConfigFile (".myrc", "env_var", "--rcfile", 
    ...).  If it is invoked with "foo --rcfile .otherrc ..." then the file 
    ".otherrc" is parsed (and ".myrc" and the contents of `env_var' are 
    ignored), otherwise ".myrc" is read.
`enableInclude'
  Allows the use of the INCLUDE section in the configuration file(s).
`skipUnknownSection'
  Unless this is TRUE, any unknown (ie, not registered) section name will cause
  an error message to be written and will terminate the program.
  
If you want to allow the user to specify configuration files in addition to the
default one, you can add a command line option "--include-config <config-file>"
with  Parameter.include. CmdLineOption ("--include-config", "$1").



Command line options are interpreted in a two step process.  An option is 
registered with a section, and for a recognized option a string is constructed 
that is parsed as if it is part of one of the configuration file's section.

To register an option, call
  PROCEDURE (s: Section) CmdLineOption* (cmdNames, cmdValue: ARRAY OF CHAR);
where `s' is the section whose value is modified by this option, `cmdName' is a
comma seperated list of option name (example: "-b,--browse", no space allowed 
in this string), and `cmdValue' a string that is evaluated by section `s'.  The
string can contain "$1", "$2", etc, they will be replaced by the first, second,
etc argument following the option name.  Example: For the section `options' 
from module `ParamOptions' command line options are registered as
  ParamOptions.options. CmdLineOption ("-w,--warnings", "warnings:=TRUE");
  ParamOptions.options. CmdLineOption ("--limit", "limitLength:=$1");
  
The command line is evaluated by calling
  PROCEDURE ParseCmdLine (optionsStartWithDash, multSingleChar, 
                          enableDashDash: BOOLEAN): INTEGER;
This procedure is defined in `Parameters'.  Its parameters mean
`optionsStartWithDash'
  If TRUE, assume that each option starts with a `-' and barf if a string 
  starting with `-' doesn't match any registered option.  Otherwise every 
  string that doesn't match a registered option is considered to be the first 
  non-option argument and evaluating stops there.
`multSingleChar'
  If TRUE, any option "-xyz" that doesn't match a registered option is 
  interpreted as "-x -y -z", otherwise it's considered as an error.
`enableDashDash'
  If TRUE, all arguments following "--" are treated as non-option arguments.
Result is the number of arguments following the last interpreted option.

The remaining arguments that are not options can be retrieved with
  PROCEDURE GetArg (index: INTEGER; VAR arg: ARRAY OF CHAR);
where `0 <= index < result(ParseCmdLine)'.  `GetArg(0,str)' will store the 
first additional argument in `str'.

*)
