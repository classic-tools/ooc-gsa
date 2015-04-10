(*	$Id: RCS.Mod,v 1.5 1997/02/03 07:31:11 acken Exp $	*)
MODULE RCS;
(*  Interface between scanner and RCS version control system.
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


IMPORT
  Rts, Str := Strings, Filenames, Files;
  

CONST
  sizePath = 256;                        
  (* length of longest possible file name plus 1 *)
  rcsSuffix = ",v";
  (* suffix of RCS master files, usually ",v" or ""; note that only a single 
     suffix is supported *)
  rcsDir = "RCS";
  (* RCS subdirectory name *)
  rcsCheckOut = "co -q ";
  (* command to check out a given file *)
  dirSep = "/";
  (* character that seperates directories in a file path *)
  
  
  
PROCEDURE MasterFile* (fileName: ARRAY OF CHAR): BOOLEAN;
(* Returns TRUE if `fileName' looks like an RCS master file.  If a non-empty
   suffix is set it is simply tested whether `fileName' ends with this string,
   otherwise (the suffix is empty) whether `fileName' refers to a file in an
   subdirectory RCS.  *)
  VAR
    p0, p1: ARRAY sizePath OF CHAR;
    pos, i: INTEGER;
    found: BOOLEAN;
  BEGIN
    IF (rcsSuffix # "") THEN   (* non-empty suffix set *)
      pos := Str.Length (fileName)-Str.Length (rcsSuffix);
      IF (pos <= 0) THEN
        RETURN FALSE
      ELSE
        Str.FindNext (rcsSuffix, fileName, pos, found, i);
        RETURN found & (pos = i)
      END
    ELSE  
      (* suffix is empty, ie `fileName' has to refer to a file in subdirectory
         named `rcsDir'  *)
      Filenames.GetPath (fileName, p0, p1);
      IF (p1 # "") & (p0 # "") THEN
        IF (p0[Str.Length (p0)-1] = dirSep) THEN
          p0[Str.Length (p0)-1] := 0X
        END;
        Filenames.GetPath (fileName, p0, p1);
        RETURN (p1 = rcsDir)
      ELSE
        RETURN FALSE
      END
    END
  END MasterFile;

PROCEDURE Master2File* (rcsFile: ARRAY OF CHAR; VAR workFile: ARRAY OF CHAR);
(* Translates the name of a master file into that of the working file.
   pre: `MasterFile(rcsFile) = TRUE'
   post: `workFile' contains `rcsFile', stripped of "<rscDir>" and the suffix
     `rcsSuffix'.
   example: (rcsSuffix=",v") "RCS/abc,v" -> "abc", "dir/abc,v" -> "dir/abc" 
            (rcsSuffix="")  "RCS/foo" -> "foo" *)            
  VAR
    path, file, dir, dirpath: ARRAY sizePath OF CHAR;
  BEGIN
    Filenames.GetPath (rcsFile, path, file);
    (* strip suffix from `file' *)
    file[Str.Length(file)-Str.Length (rcsSuffix)] := 0X;
    (* strip subdirectory from path *)
    IF (path # "") THEN
      IF (path[Str.Length (path)-1] = dirSep) THEN
        path[Str.Length (path)-1] := 0X
      END;
      Filenames.GetPath (path, dirpath, dir);
      IF (dir = rcsDir) THEN
        COPY (dirpath, path)
      END
    END;
    (* assemble name of working file *)
    Filenames.BuildFilename (workFile, path, file, "") 
  END Master2File;


PROCEDURE CheckOut* (VAR fileName: ARRAY OF CHAR; 
                     VAR resultMsg: ARRAY OF CHAR): BOOLEAN;
(* Runs checksout on the RCS file `fileName'.  
   pre: `fileName' is the name of a master file.
   post: If `fileName' exists it is converted into the name of a working file.
     A checkout is attempted on this filename.  Result is TRUE if it succeeds
     and the checkout command is returned in `resultMsg', otherwise an error
     message is put into `resultMsg' and FALSE is returned.  *)
  VAR
    com: ARRAY 3*sizePath OF CHAR;
  BEGIN
    (* first check if the RCS file can be opened (ie, if it exists) *)
    IF Files.Exists (fileName) THEN
      (* change `fileName' to hold the name of the work file *)
      Master2File (fileName, fileName); 
      (* assemble command to check out the latest revision *)
      com := rcsCheckOut;
      Str.Append (fileName, com);
      IF (Rts.System (com) # 0) THEN
        COPY (com, resultMsg);
        Str.Insert ("`", 0, resultMsg);
        Str.Append ("' failed", resultMsg);
        RETURN FALSE
      ELSE
        COPY (com, resultMsg);
        RETURN TRUE
      END
    ELSE
      COPY ("Could not open RCS file ", resultMsg);
      Str.Append (fileName, resultMsg);
      RETURN FALSE
    END
  END CheckOut;

PROCEDURE FindMasterFile* (VAR fileName: ARRAY OF CHAR): BOOLEAN;
(* Searches for a RCS master file for `fileName'.  If such a file is found its
   name is copied into `fileName' and result is TRUE.  *)
  VAR
    path, file, master: ARRAY sizePath OF CHAR;
  BEGIN
    Filenames.GetPath (fileName, path, file);
    (* first test for "path/<rcsDir>/file<rcsSuffix>" *)
    Str.Append (rcsSuffix, file);
    Filenames.AddPath (master, path, rcsDir);
    Filenames.BuildFilename (master, master, file, "");
    IF ~Files.Exists (master) & (rcsSuffix # "") THEN
      (* now try "path/file<rcsSuffix>" *)
      Filenames.BuildFilename (master, path, file, "")
    END;
    IF Files.Exists (master) THEN
      COPY (master, fileName);
      RETURN TRUE
    ELSE
      RETURN FALSE
    END
  END FindMasterFile;

END RCS.
