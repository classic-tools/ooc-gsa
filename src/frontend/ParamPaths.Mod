(* 	$Id: ParamPaths.Mod,v 1.12 1999/08/08 18:28:15 acken Exp $	 *)
MODULE ParamPaths;
(*  Parsing and maintenance of path lists, locating files.
    Copyright (C) 1995, 1996, 1997, 1999  Michael van Acken

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
Implements configuration file sections PATHS and NEWFILES.  They contain lists
of paths that are searched for a given file, respectively define in which 
directory a  new file has to be placed. 

Syntax:
  path              = ( name | string ) [";"].
  wildcard          = name | string.
  wildcard_list     = wildcard {[","] wildcard}.
  wildcard_rcs      = wildcard ["[" "RCS" "]"].
  wildcard_list_rcs = wildcard_rcs  {[","] wildcard_rcs}.
  dest_pattern      = "PUT" wildcard_list "INTO" path.
  source_pattern    = "GET" wildcard_list_rcs "FROM" path {path}.
  paths_section     = "PATHS" {source_pattern} "END".
  new_files_section = "NEWFILES" {dest_pattern} "END".

Example:
  PATHS 
  GET *.Mod [RCS] FROM 
    .
    /usr/local/lang/o2c/lib
  GET *.c FROM 
    obj
    /usr/local/lang/o2c/obj
  END
  NEWFILES
  PUT *.c *.h *.o INTO obj
  END

The procedures `FindPath' and `FindPathExt' search the pattern list in PATHS 
in the order in which they are written.  If a pattern matches a file name, the 
corresponding path list is searched from left to right, and the first path that
contains the file is returned.  If the pattern is marked with "[RCS]", then
the procedure looks first for the file itself, then for a RCS master file.
The complete path of the file (including the file name and a possible
RCS suffix) is returned.  See also the description of `FindPath'. 
The procedures `GeneratePath' and `GeneratePathExt' search the pattern list in 
NEWFILES (or PATHS, if no NEWFILES is present or does not contain a matching
pattern, and `Init' was called appropiately).  If a pattern matches a file 
name, the corresponding path (or the first one of the path list) is taken for 
the file's directory.  The complete file path is returned, or, if no matching 
pattern is found, only the file name itself.  See also the description for 
`GeneratePath' and `Init'.
*)
   
IMPORT 
  Out, Strings, Strings2, Filenames, Param := Parameter, VC := RCS, Files;
  
TYPE
  Path* = POINTER TO PathDesc;
  PathDesc* = RECORD
    next-: Path;                         
    (* next path in `Pattern.pathList' *)
    path-: Param.String;
    (* path string *)
  END;
  Pattern* = POINTER TO PatternDesc;
  PatternDesc* = RECORD
    next-: Pattern;                      
    (* next pattern in `PathsSection.patternList' *)
    filePattern-: Param.String;
    (* wildcard pattern *)
    rcsIsEnabled-: BOOLEAN;
    (* RCS files are searched for this pattern *)
    pathList-: Path;
    (* list of paths associated with this pattern, linked with `Path.next' *)
  END;
  
  PathsSection* = POINTER TO PathsSectionDesc;
  PathsSectionDesc* = RECORD
    (Param.SectionDesc)
    patternList-: Pattern;
    (* list of patterns in this section, linked with `Pattern.next' *)
    rcsEnabled-: BOOLEAN;
    (* TRUE if a pattern in this section is marked with [RCS] *)
  END;
  NewFilesSection* = POINTER TO NewFilesDesc;
  NewFilesDesc* = RECORD
    (PathsSectionDesc)
  END;

VAR
  paths-: PathsSection;
  (* PATHS section, always #NIL *)
  newFiles-: NewFilesSection;
  (* NEWFILES section, always #NIL *)
  usePaths: BOOLEAN;
  (* use paths in the PATHS section for GeneratePath in the absence of a
     NEWFILES section *)


PROCEDURE (s: PathsSection) AddPattern* (p: Pattern);
(* Adds a (not necessarily unique) pattern to the end of the pattern list in
   `p'. *)
  PROCEDURE Add (VAR list: Pattern);
    BEGIN
      IF (list = NIL) THEN
        list := p
      ELSE
        Add (list. next)
      END
    END Add;
    
  BEGIN
    p. next := NIL;
    Add (s. patternList)
  END AddPattern;


PROCEDURE ParsePatterns (s: PathsSection; includeEnd, sourceSect: BOOLEAN);
(* Reads a list a patterns from the input stream `Param.in'. 
   If `includeEnd=TRUE', then the keyword END is recognized to terminate this 
   section, otherwise it'll be parsed til `Param.in. eos=TRUE'.  
   `sourceSect=TRUE' expects the keywords GET/FROM and allows to place "[RCS]"
   behind the file pattern, so that RCS files are found with FindPath.  
   Otherwise the expected keywords are PUT/INTO.  *)
  CONST
    string=0; get=1; from=2; put=3; into=4; comma=5; semicolon=6; end=7; eof=8;
  VAR
    sym: SHORTINT;
    str: Param.Filename;
    paths: Path;
    pattern, patterns, next: Pattern;
  
  PROCEDURE Next (sep: ARRAY OF CHAR);
    BEGIN
      IF Param.in. LookingAtString (str) THEN
        sym := string;
      ELSIF Param.in. eos THEN
        sym := eof
      ELSIF (Param.in. currChar = ",") THEN
        Param.in. currSymPos := Param.in. CurrPos(); Param.in. NextChar;
        sym := comma
      ELSIF (Param.in. currChar = ";") THEN
        Param.in. currSymPos := Param.in. CurrPos(); Param.in. NextChar;
        sym := semicolon
      ELSE
        Param.in. ReadName (sep, str);
        IF (str = "GET") THEN sym := get
        ELSIF (str = "FROM") THEN sym := from
        ELSIF (str = "PUT") THEN sym := put
        ELSIF (str = "INTO") THEN sym := into
        ELSIF includeEnd & (str = "END") THEN sym := end
        ELSE sym := string
        END
      END
    END Next;
  
  PROCEDURE PathList (multiple: BOOLEAN): Path;
  (* Reads (non-empty) list of paths. *)
    VAR
      list, path: Path;
      
    PROCEDURE NewPath (VAR str: ARRAY OF CHAR): Path;
      VAR
        path: Path;
      BEGIN
        NEW (path);
        NEW (path. path, Strings.Length (str)+1);
        COPY (str, path. path^);
        path. next := NIL;
        RETURN path
      END NewPath;
    
    BEGIN
      Next (";");
      list := NIL;
      REPEAT
        IF (sym # string) THEN
          Param.in. Error (Param.currSym, "File path expected"); RETURN NIL
        ELSE
          IF (list = NIL) THEN
            list := NewPath (str);
            path := list
          ELSE
            IF ~multiple THEN
              Param.in. Error (Param.currSym, "Only one destination path allowed"); 
              RETURN NIL
            END;
            path. next := NewPath (str);
            path := path. next
          END;
          Next (";");
          IF (sym = semicolon) THEN
            Next (";")
          END
        END
      UNTIL (sym # string);
      RETURN list
    END PathList;
  
  PROCEDURE PatternList(): Pattern;
    VAR
      list, pattern: Pattern;
      
    PROCEDURE CheckForRCS (): BOOLEAN;
    (* Returns TRUE if the sequence "[RCS]" is following, FALSE otherwise. *)
      BEGIN
        Param.in. SkipWhitespace;
        IF (Param.in. currChar = "[") THEN
          Param.in. NextChar;
          Param.in. Match ("RCS");
          IF ~sourceSect THEN
            Param.in. Error (Param.currSym, "Can't specify RCS support here")
          END;
          Param.in. Match ("]");
          s. rcsEnabled := TRUE;
          RETURN TRUE
        ELSE
          RETURN FALSE
        END
      END CheckForRCS;

    PROCEDURE NewPattern (wildcard: ARRAY OF CHAR; 
                          rcsIsEnabled: BOOLEAN): Pattern;
    (* Creates new file pattern from `wildcard' and `rcsIsEnabled'. *)
      VAR
        pattern: Pattern;
      BEGIN
        NEW (pattern);
        pattern. next := NIL;
        NEW (pattern. filePattern, Strings.Length (wildcard)+1);
        COPY (wildcard, pattern. filePattern^);
        pattern. rcsIsEnabled := rcsIsEnabled;
        RETURN pattern
      END NewPattern;

    BEGIN
      Next (",[");
      IF (sym # string) THEN
        Param.in. Error (Param.currSym, "Wildcard string expected"); RETURN NIL
      ELSE
        list := NewPattern (str, CheckForRCS());
        pattern := list;
        LOOP
          Next (",[");
          IF (sym # comma) & (sym # string) THEN
            RETURN list
          ELSE
            IF (sym = comma) THEN
              Next (",[")
            END;
            IF (sym # string) THEN
              Param.in. Error (Param.currSym, "Wildcard string expected"); 
              RETURN NIL
            ELSE
              pattern. next := NewPattern (str, CheckForRCS());
              pattern := pattern. next
            END
          END
        END
      END
    END PatternList;
  
  BEGIN
    Next (",;");
    WHILE (sym # eof) & (sym # end) DO
      patterns := NIL; paths := NIL;
      IF sourceSect THEN
        IF (sym = get) THEN
          patterns := PatternList ();
          IF (sym # from) THEN
            Param.in. Error (Param.currSym, "FROM expected");
          ELSE
            paths := PathList (TRUE)
          END
        ELSE
          Param.in. Error (Param.currSym, "GET expected")
        END
      ELSE
        IF (sym = put) THEN
          patterns := PatternList();
          IF (sym # into) THEN
            Param.in. Error (Param.currSym, "INTO expected");
          ELSE
            paths := PathList (FALSE)
          END
        ELSE
          Param.in. Error (Param.currSym, "PUT expected")
        END
      END;
      IF (patterns = NIL) OR (paths = NIL) THEN
        RETURN
      ELSE
        (* set paths for each pattern and add it to section *)
        pattern := patterns;
        WHILE (pattern # NIL) DO
          pattern. pathList := paths;
          next := pattern. next;
          s. AddPattern (pattern);
          pattern := next
        END
      END
    END;
    IF includeEnd & (sym # end) THEN
      Param.in. Error (Param.currSym, "END expected")
    END
  END ParsePatterns;

PROCEDURE (s: PathsSection) Parse* (includeEnd: BOOLEAN);
(* Parses PATHS section, allows [RCS] after file pattern. *)
  BEGIN
    ParsePatterns (s, includeEnd, TRUE)
  END Parse;

PROCEDURE (s: NewFilesSection) Parse* (includeEnd: BOOLEAN);
(* Parses NEWFILES section, doesn't accept [RCS] after file pattern. *)
  BEGIN
    ParsePatterns (s, includeEnd, FALSE)
  END Parse;

PROCEDURE (s: PathsSection) Write*;
(* Writes paths in section `s'. *)
  VAR
    p: Pattern;
    
  PROCEDURE WritePaths (pathList: Path);
    BEGIN
      Out.String (pathList. path^);
      WHILE (pathList. next # NIL) DO
        pathList := pathList. next;
        Out.String ("; ");
        Out.String (pathList. path^)
      END
    END WritePaths;
  
  BEGIN
    p := s. patternList;
    WHILE (p # NIL) DO
      IF (s IS NewFilesSection) THEN
        Out.String ("  PUT ")
      ELSE
        Out.String ("  GET ")
      END;
      Out.String (p. filePattern^);
      IF p. rcsIsEnabled THEN
        Out.String (" [RCS]")
      END;
      IF (s IS NewFilesSection) THEN
        Out.String (" INTO ")
      ELSE
        Out.String (" FROM ")
      END;
      WritePaths (p. pathList);
      Out.Ln;
      p := p. next
    END
  END Write;


PROCEDURE FindPath* (fileName: ARRAY OF CHAR; keepGivenPath: BOOLEAN;
                     VAR filePath: ARRAY OF CHAR): BOOLEAN;
(* Tries to locate a file `fileName' in one of the paths stored in the 
   PATHS section.
     The section is searched (from the beginning) for a pattern matching 
   `fileName'.  If one is found it tries to locate `fileName' in one of the 
   directories associated with that pattern, searching the path list from 
   left to right.
     Files are tested for existence in the following order 1) path/fileName 
   and 2) RCS_MASTER(path/fileName), if RCS is enabled.  On success the 
   complete name of the file found is stored in `filePath', result is TRUE.  If
   no file is found the search for another matching pattern continues.  
     Only if no more patterns are available the file `fileName' and its RCS 
   master are considered, the latter only if any matching pattern had the RCS 
   flag set.
     Setting the `keepGivenPath' flag prevents searching the path lists, if, 
   and only if, `fileName' has a non-empty directory part. 
   
   post: Result is TRUE if a valid `filePath' (ie, a working file or a RCS 
     master) could be constructed that is known to exist.  Otherwise result is
     FALSE and `filePath' is equal to `fileName'.  *)
  VAR
    pattern: Pattern;
    path: Path;
    dirPart, filePart: Param.Filename;
    rcsEnabled, searchPaths: BOOLEAN;
  BEGIN
    Filenames.GetPath (fileName, dirPart, filePart);
    (* search path list if `fileName' has no directory part or if 
       `keepGivenPath' isn't set *)
    searchPaths := ~keepGivenPath OR (dirPart = "");
    rcsEnabled := FALSE;
    pattern := paths. patternList;
    WHILE (pattern # NIL) DO             (* scan all pattern descriptions *)
      IF Strings2.Match (pattern. filePattern^, fileName) THEN
        rcsEnabled := rcsEnabled OR pattern. rcsIsEnabled;
        IF searchPaths THEN
          path := pattern. pathList;
          WHILE (path # NIL) DO (* scan paths associated with matching pattern *)
            Filenames.AddPath (filePath, path. path^, fileName);
            Filenames.ExpandPath (filePath, filePath);
            IF Files.Exists (filePath) OR 
               pattern. rcsIsEnabled & VC.FindMasterFile (filePath) THEN
              (* file (or its RCS master file) exists *)
              RETURN TRUE
            END;
            path := path. next
          END
        END
      END;
      pattern := pattern. next  (* no luck til now, try next pattern *)
    END;
    (* nothing found, last try is the current directory *)
    COPY (fileName, filePath);
    RETURN Files.Exists (filePath) OR
           rcsEnabled & VC.FindMasterFile (filePath)
  END FindPath;
  
PROCEDURE GeneratePath* (fileName: ARRAY OF CHAR; VAR filePath: ARRAY OF CHAR);
(* Produces a file name (including the path information) for the file 
   `fileName'.
   post: The NEWFILES section (or, if none is present or there is no matching 
     pattern in NEWFILES, the PATHS section; this depends on the parameters to 
     `Init') is searched for the first pattern matching `fileName'.  
     The first path associated with that pattern will be used as the file's
     path. The complete name is then stored in `filePath'.
     If no pattern is found `path' will be set to the value in `fileName', i.e.
     the file will be placed in the current directory. *)
  VAR
    pattern: Pattern;
    found: BOOLEAN;
  BEGIN
    found := FALSE;
    
    IF (newFiles. defined OR (newFiles. patternList # NIL)) THEN
      (* scan all pattern descriptions in NEWFILES *)
      pattern := newFiles. patternList;
      WHILE ~found & (pattern # NIL) DO
        IF Strings2.Match (pattern. filePattern^, fileName) THEN
          Filenames.AddPath (filePath, pattern. pathList. path^, fileName);
          Filenames.ExpandPath (filePath, filePath);
          found := TRUE
        END;
        pattern := pattern. next
      END
    END;
    
    IF usePaths THEN
      (* scan all pattern descriptions in PATHS *)
      pattern := paths. patternList;
      WHILE ~found & (pattern # NIL) DO
        IF Strings2.Match (pattern. filePattern^, fileName) THEN
          Filenames.AddPath (filePath, pattern. pathList. path^, fileName);
          Filenames.ExpandPath (filePath, filePath);
          found := TRUE
        END;
        pattern := pattern. next
      END
    END;
    
    IF ~found THEN
      (* nothing suitable found: use given file name *)
      COPY (fileName, filePath)
    END
  END GeneratePath;


PROCEDURE FindPathExt* (fileName, ext: ARRAY OF CHAR;  keepGivenPath: BOOLEAN;
                        VAR filePath: ARRAY OF CHAR): BOOLEAN;
(* Like FindPath, but `fileName' is build like "<name>.<ext>". *)
  VAR
    file: Param.Filename;
  BEGIN
    COPY (fileName, file);
    Strings2.AppendChar (".", file);
    Strings.Append (ext, file);
    RETURN FindPath (file, keepGivenPath, filePath)
  END FindPathExt;

PROCEDURE GeneratePathExt* (fileName, ext: ARRAY OF CHAR; VAR filePath: ARRAY OF CHAR);
(* Like GeneratePath, but `fileName' is build like "<name>.<ext>". *)
  VAR
    file: Param.Filename;
  BEGIN
    COPY (fileName, file);
    Strings2.AppendChar (".", file);
    Strings.Append (ext, file);
    GeneratePath (file, filePath)
  END GeneratePathExt;


PROCEDURE Init* (sectionPaths, sectionNewFiles, fallBackToPaths: BOOLEAN);
(* Registers the paths sections for configuration files.
     sectionPaths:  Register section `PATHS', whose contents are used for the 
       procedures FindPath and FindPathExt.
     sectionNewFiles:  Register section `NEWFILES', whose contents are used 
       for the procedures GeneratePath and GeneratePathExt.
     fallBackToPaths:  Determines how new file names are built by GeneratePath
       and GeneratePathExt in the absence of a NEWFILES section, or if no 
       pattern in NEWFILES matches.  If TRUE, the first paths from the lists in
       PATHS are used to place the new files, otherwise the current directory. 
*)
  BEGIN
    usePaths := fallBackToPaths;
    IF sectionPaths THEN
      Param.AddSection ("PATHS", paths)
    END;
    IF sectionNewFiles THEN
      Param.AddSection ("NEWFILES", newFiles)
    END
  END Init;

BEGIN
  NEW (paths);
  paths. rcsEnabled := FALSE;
  paths. patternList := NIL;
  NEW (newFiles);
  paths. rcsEnabled := FALSE;
  newFiles. patternList := NIL
END ParamPaths.
