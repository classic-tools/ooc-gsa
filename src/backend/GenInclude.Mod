(*	$Id: GenInclude.Mod,v 1.8 1997/10/13 11:56:16 acken Exp $	*)
MODULE GenInclude;
(*  Writes include statments.
    Copyright (C) 1996, 1997  Michael van Acken

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
  Str := Strings, Strings2, TextRider, Parameter, ParamPaths, Filenames,
  D := Data, Sym := SymbolTable, StdTypes;


PROCEDURE IncludeFile* (w: TextRider.Writer; name, suffix: ARRAY OF CHAR);
(* Writes include statement `#include "<name><suffix>"'.  *)
  BEGIN
    w. WriteLn;
    w. WriteString ('#include "');
    w. WriteString (name);
    w. WriteString (suffix);
    w. WriteChar ('"');
  END IncludeFile;

PROCEDURE Include* (w: TextRider.Writer; module: D.Object; 
                    suffix: ARRAY OF CHAR; ignoreFlag: BOOLEAN);
(* Writes an include statement for the file "<module name><suffix>" and sets
   the flag `StdTypes.objIncluded' in `module. beFlags'.  `suffix' should be 
   either ".h" or ".d".  If `module' refers to a predefined module, or
   the include statement has already been written, then nothing is done.  
   With `ignoreFlags=TRUE' the include is written even if `objIncluded' is 
   already set.  *)
  BEGIN
    IF ((module. moduleId = D.noSymbolTable) OR
        (module. moduleId > Sym.predefModuleId)) &
       (ignoreFlag OR ~(StdTypes.objIncluded IN module. beFlags)) THEN
      IncludeFile (w, module. name^, suffix);
      INCL (module. beFlags, StdTypes.objIncluded)
    END
  END Include;

PROCEDURE AddOptions* (appCom: PROCEDURE (opt: ARRAY OF CHAR));
(* Adds include directories to the C compiler option list.  Any path rule is
   checked whether it matches any .h file names.  If it does, its directories
   are appended as -I<dir>.  Finally an option -I- is added to prevent gcc (and
   maybe other compilers) applying the names to `#include <..>' statements.  *)
  CONST
    sizeBuffer = 256;
  VAR
    pattern: ParamPaths.Pattern;
    path: ParamPaths.Path;
    filename: Parameter.Filename;
    pathArray: ARRAY sizeBuffer OF ParamPaths.Path;
    pathCounter: INTEGER;
    
  PROCEDURE MatchesHeader (pattern: ARRAY OF CHAR): BOOLEAN;
  (* Returns TRUE if the given pattern matches file names with a .h or .d 
     suffix.  *)
    VAR
      i, len: INTEGER;
      suffix: ARRAY 256 OF CHAR;
    BEGIN
      len := Str.Length (pattern);
      (* first check whether a . is present in the pattern *)
      i := len-1;
      WHILE (i >= 0) & (pattern[i] # ".") DO
        DEC (i)
      END;
      
      (* check if suffix pattern matches .h *)
      IF (i >= 0) THEN   (* i is position of last . in pattern *)
        Str.Extract (pattern, i, MAX(INTEGER), suffix);
        IF Strings2.Match (suffix, ".h") OR
           Strings2.Match (suffix, ".d") THEN
          RETURN TRUE
        END
      END;
      
      (* check all suffix matches *)
      i := len-1;
      WHILE (i >= 0) DO
        IF (pattern[i] = "*") OR (pattern[i] = "?") THEN
          Str.Extract (pattern, i, MAX(INTEGER), suffix);
          IF Strings2.Match (suffix, ".h") OR
             Strings2.Match (suffix, ".d") THEN
            RETURN TRUE
          END
        END;
        DEC (i)
      END;
      RETURN FALSE
    END MatchesHeader;
  
  PROCEDURE Duplicate (VAR str: ARRAY OF CHAR): BOOLEAN;
  (* Returns TRUE if an include path for directory `str' has already been added
     to the option list.  *)
    VAR
      i: INTEGER;
    BEGIN
      FOR i := 0 TO pathCounter-1 DO
        IF (str = pathArray[i]. path^) THEN
          RETURN TRUE
        END
      END;
      RETURN FALSE
    END Duplicate;
  
  PROCEDURE ContainsBlanks (VAR str: ARRAY OF CHAR): BOOLEAN;
  (* Returns TRUE if `str' contains one or more blanks.  *)
    VAR
      i: INTEGER;
    BEGIN
      i := 0;
      WHILE (str[i] # 0X) & (str[i] # " ") DO
        INC (i)
      END;
      RETURN (str[i] = " ")
    END ContainsBlanks;
  
  BEGIN
    pathCounter := 0;
    pattern := ParamPaths.paths. patternList;
    WHILE (pattern # NIL) DO
      IF MatchesHeader (pattern. filePattern^) THEN
        path := pattern. pathList;
        WHILE (path # NIL) DO
          IF ~Duplicate (path. path^) THEN
            COPY (path. path^, filename);
            Filenames.ExpandPath (filename, filename);
            IF ContainsBlanks (filename) THEN
              appCom (' "-I');
              appCom (filename);
              appCom ('"')
            ELSE
              appCom (" -I");
              appCom (filename)
            END;
            IF (pathCounter < sizeBuffer) THEN
              (* keep track of written paths to avoid duplicates *)
              pathArray[pathCounter] := path;
              INC (pathCounter)
            END
          END;
          path := path. next
        END
      END;
      pattern := pattern. next
    END;

    (* make sure, that the previous paths are only used for the ".." includes,
       and not for the <..> ones; this should avoid confusion if names of 
       system and oo2c header files overlap; don't know if any compilers 
       apart from gcc support this, but it shouldn't hurt any of them *)
    appCom (" -I-")
  END AddOptions;

END GenInclude.
