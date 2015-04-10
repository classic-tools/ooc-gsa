(*	$Id: FileData.Mod,v 1.10 1999/11/06 15:35:07 ooc-devel Exp $	*)
MODULE FileData;
(*  Access layer for file attributes.
    Copyright (C) 1996-1997, 1999  Michael van Acken

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
  Rts, Termination, Strings, Files, Time, Parameter, ParamPaths, Data;
  
  
TYPE
  FileData* = POINTER TO FileDataDesc;
  Dependence = POINTER TO DependenceDesc;
  FileDataDesc = RECORD
    nextFile: FileData;
    
    name*: Data.String;
    suffix: ARRAY 8 OF CHAR;
    
    flags-: SET;
    filename-: Data.String;
    timeStamp-: Time.TimeStamp;
    
    dependenceList: Dependence
  END;
  DependenceDesc = RECORD
    nextDep: Dependence;
    file: FileData
  END;

CONST
  filenameSet = 0;
  (* set in `FileData.flags' if the field `filename' holds a file name (i.e. 
     isn't NIL *)
  timeStampSet = 1;
  fileExists* = 2;
  
VAR
  fileList: FileData;


TYPE 
  FileList = POINTER TO FileListDesc;
  FileListDesc = RECORD
    next: FileList;
    name: POINTER TO ARRAY OF CHAR
  END;

VAR
  removalList: FileList;


PROCEDURE MarkForRemoval* (name, suffix: ARRAY OF CHAR);
  VAR
    len: LONGINT;
    fl: FileList;
  BEGIN
    len := Strings.Length (name)+Strings.Length (suffix)+1;
    NEW (fl);
    fl. next := removalList;
    NEW (fl. name, len);
    COPY (name, fl. name^);
    Strings.Append (suffix, fl. name^);
    removalList := fl
  END MarkForRemoval;


PROCEDURE GetFile* (name, suffix: ARRAY OF CHAR): FileData;
  VAR
    file: FileData;
    
  PROCEDURE InitFile (file: FileData; VAR name, suffix: ARRAY OF CHAR);
    BEGIN
      file. nextFile := fileList;
      NEW (file. name, Strings.Length (name)+1);
      COPY (name, file. name^);
      COPY (suffix, file. suffix);
      file. flags := {};
      file. filename := NIL;
      file. dependenceList := NIL;
      fileList := file
    END InitFile;
  
  BEGIN
    file := fileList;
    WHILE (file # NIL) & ((file. name^ # name) OR (file. suffix # suffix)) DO
      file := file. nextFile
    END;
    IF (file = NIL) THEN
      NEW (file);
      InitFile (file, name, suffix)
    END;
    RETURN file
  END GetFile;

PROCEDURE AddDependence* (file: FileData; depName, depSuffix: ARRAY OF CHAR);
  VAR
    dep: Dependence;
    depFile: FileData;
  BEGIN
    dep := file. dependenceList;
    WHILE (dep # NIL) & 
          ((dep. file. name^ # depName) OR (dep. file. suffix # depSuffix)) DO
      dep := dep. nextDep
    END;
    IF (dep = NIL) THEN
      depFile := GetFile (depName, depSuffix);
      NEW (dep);
      dep. file := depFile;
      dep. nextDep := file. dependenceList;
      file. dependenceList := dep
    END
  END AddDependence;

PROCEDURE SetFilename* (file: FileData; VAR filename: ARRAY OF CHAR);
  BEGIN
    NEW (file. filename, Strings.Length (filename)+1);
    COPY (filename, file. filename^);
    INCL (file. flags, filenameSet)
  END SetFilename;

PROCEDURE SetTimeStamp* (file: FileData);
  VAR
    msg: ARRAY Parameter.sizeFilename+35 OF CHAR;
    res: Files.Result;
  BEGIN
    IF ~(timeStampSet IN file. flags) THEN
      Files.GetModTime (file. filename^, file. timeStamp, res);
      IF (res # Files.done) THEN
        msg := "Failed to retrive time stamp of `";
        Strings.Append (file. filename^, msg);
        Strings.Append ("'", msg);
        Parameter.FatalError (msg)
      END;
      INCL (file. flags, timeStampSet)
    END
  END SetTimeStamp;

PROCEDURE FindFile* (name, suffix: ARRAY OF CHAR; timeStamp: BOOLEAN): FileData;
  VAR
    file: FileData;
    filename: Parameter.Filename;
    found: BOOLEAN;
  BEGIN
    ASSERT (suffix[0] = ".");
    file := GetFile (name, suffix);
    Strings.Delete (suffix, 0, 1);
    IF ~(filenameSet IN file. flags) THEN
      found := ParamPaths.FindPathExt (name, suffix, FALSE, filename);
      SetFilename (file, filename);
      IF found THEN
        INCL (file. flags, fileExists)
      END
    ELSE
      found := TRUE
    END;
    IF found & timeStamp THEN
      SetTimeStamp (file)
    END;
    RETURN file
  END FindFile;

PROCEDURE NewFile* (name, suffix: ARRAY OF CHAR): FileData;
  VAR
    file: FileData;
    filename: Parameter.Filename;
  BEGIN
    file := GetFile (name, suffix);
    IF (suffix[0] = ".") THEN
      Strings.Delete (suffix, 0, 1);
      ParamPaths.GeneratePathExt (name, suffix, filename)
    ELSE
      ParamPaths.GeneratePath (name, filename)
    END;
    SetFilename (file, filename);
    INCL (file. flags, fileExists);
    RETURN file
  END NewFile;

PROCEDURE ClearFiles*;
  BEGIN
    fileList := NIL
  END ClearFiles;


PROCEDURE RemoveFiles*;
(* Remove all files that were previously marked with `MarkForRemoval'.  *)
  CONST
    sizeCmd = 2*1024;
  VAR
    cmd: ARRAY sizeCmd OF CHAR;
    cmdLen: INTEGER;
    fl: FileList;
  
  PROCEDURE ExecCmd;
    VAR
      dummy: LONGINT;
    BEGIN
      IF (cmdLen # 0) THEN
        dummy := Rts.System (cmd);
        cmdLen := 0
      END
    END ExecCmd;
  
  PROCEDURE AddFile (VAR file: ARRAY OF CHAR);
    VAR
      len: INTEGER;
    BEGIN
      len := Strings.Length (file);
      IF (cmdLen+len+2 >= sizeCmd) THEN
        ExecCmd
      END;
      IF (cmdLen = 0) THEN
        COPY ("rm -f", cmd);
        cmdLen := Strings.Length (cmd)
      END;
      cmd[cmdLen] := " ";
      cmd[cmdLen+1] := 0X;
      Strings.Append (file, cmd);
      INC (cmdLen, len+1)
    END AddFile;
  
  BEGIN
    cmdLen := 0;
    WHILE (removalList # NIL) DO
      fl := removalList;
      removalList := fl. next;
      AddFile (fl. name^)
    END;
    ExecCmd
  END RemoveFiles;

BEGIN
  removalList := NIL;
  ClearFiles;
  Termination.RegisterProc (RemoveFiles)
END FileData.
