(*      $Id: External.Mod,v 1.8 1999/11/06 15:35:16 ooc-devel Exp $       *)
MODULE External;
(*  Handles data on external C files and libraries.
    Copyright (C) 1996-1999  Michael van Acken

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
  Strings, Files, BinaryRider, IntStr,
  Parameter, ParamPaths, Config, E := Error, D := Data;


TYPE
  Ref* = POINTER TO RefDesc;
  RefDesc = RECORD
    next-, nextExt*: Ref;
    mode-: SHORTINT;
    pos*: LONGINT;
  END;

CONST  (* valid values for `Ref.mode' *)
  noRef* = 0;
  fileRef* = 1;
  objRef* = 2;
  libRef* = 3;
  libDepRef* = 4;

TYPE
  NameList* = POINTER TO NameListDesc;
  NameListDesc = RECORD
    next-: NameList;
    name-: D.String
  END;
  
  File* = POINTER TO FileDesc;
  FileDesc = RECORD
    (RefDesc)
    name-, suffix-: D.String;
    prefixOptions*, suffixOptions*: NameList;
  END;
  
  Lib* = POINTER TO LibDesc;
  Dependence* = POINTER TO DependenceDesc;
  ModuleId* = POINTER TO ModuleIdDesc;
  LibDesc = RECORD
    (RefDesc)
    nextLib: Lib;                       (* link used by `libList' *)
    name*: D.String;
    version*: D.String;
    installPath-: D.String;
    depList-: Dependence;
    modList-: ModuleId;
    prefixOptions*, suffixOptions*: NameList;
    mark: SHORTINT;
    deferred*: BOOLEAN;                 (* set by SystemFlags.ReadObjectInfo *)
    counter: INTEGER;
  END;
  DependenceDesc = RECORD
    next-: Dependence;
    lib-: Lib
  END;
  ModuleIdDesc = RECORD
    next: ModuleId;
    name-: D.String;
    magicId-: LONGINT;
  END;

VAR
  libList: Lib;
  (* holds list of all known library references: dependencies, O2 libraries, 
     and C libraries; elementes are linked through `LibDesc.nextLib'  *)

  libFileId*: ARRAY 5 OF CHAR;
  emptyString: ARRAY 2 OF CHAR;
  

PROCEDURE InitRef (ref: Ref; mode: SHORTINT);
  BEGIN
    ref. next := NIL;
    ref. nextExt := NIL;
    ref. mode := mode;
    ref. pos := D.undefPos
  END InitRef;

PROCEDURE InitFile (file: File; mode: SHORTINT; name, suffix: ARRAY OF CHAR);
  BEGIN
    InitRef (file, mode);
    NEW (file. name, Strings.Length (name)+1);
    COPY (name, file. name^);
    NEW (file. suffix, Strings.Length (suffix)+1);
    COPY (suffix, file. suffix^);
    file. prefixOptions := NIL;
    file. suffixOptions := NIL
  END InitFile;

PROCEDURE InitLib (lib: Lib; mode: SHORTINT; name, version: ARRAY OF CHAR);
  BEGIN
    InitRef (lib, mode);
    NEW (lib. name, Strings.Length (name)+1);
    COPY (name, lib. name^);
    IF (version = "") THEN
      lib. version := NIL
    ELSE
      NEW (lib. version, Strings.Length (version)+1);
      COPY (version, lib. version^)
    END;
    lib. installPath := NIL;
    lib. nextLib := NIL;
    lib. depList := NIL;
    lib. modList := NIL;
    lib. prefixOptions := NIL;
    lib. suffixOptions := NIL;
    lib. mark := 0;
    lib. deferred := FALSE;
    lib. counter := 0
  END InitLib;


PROCEDURE NewFile* (mode: SHORTINT; name, suffix: ARRAY OF CHAR; pos: LONGINT): File;
  VAR
    file: File;
  BEGIN
    NEW (file);
    InitFile (file, mode, name, suffix);
    RETURN file
  END NewFile;

PROCEDURE GetLib* (mode: SHORTINT; name, version: ARRAY OF CHAR): Lib;
(* Tries to locale library in list of cached library entries.  If no existing
   entry is found a new one is generated.  Otherwise it is checked that the old
   one is consistend with the new request.  If the requested mode is an O2 
   library and the old one a C library (or vice versa) an error is signaled.
   pre: `mode IN {libDep, libO2Ref, libCRef}'  *)
  VAR
    ptr: Lib;
    
  PROCEDURE NewLib (mode: SHORTINT; VAR name, version: ARRAY OF CHAR): Lib;
    VAR
      lib: Lib;
    BEGIN
      NEW (lib);
      InitLib (lib, mode, name, version);
      lib. nextLib := libList;
      libList := lib;
      RETURN lib
    END NewLib;
  
  BEGIN
    ptr := libList;
    WHILE (ptr # NIL) & (ptr. name^ # name) DO
      ptr := ptr. nextLib
    END;
    IF (ptr = NIL) THEN
      RETURN NewLib (mode, name, version)
    ELSE
      (* check for errors *)
      CASE mode OF
      | libDepRef:
        (* no problems if just a dependence is demanded *)
      | libRef:
        CASE ptr. mode OF
        | libDepRef:  (* promote old dependenc to library module *)
          ptr. mode := libRef
        | libRef:  (* keep old status *)
        END
      END;
      RETURN ptr 
    END
  END GetLib;

PROCEDURE ClearLibList* (leave: Lib);
(* Removes all but library `leave' from `libList'.  *)
  BEGIN
    libList := leave;
    leave. nextLib := NIL;
    leave. depList := NIL;
    leave. modList := NIL
  END ClearLibList;

PROCEDURE AddName* (VAR list: NameList; name: D.String);
(* Append `name' to list unless such an entry already exists.  *)
  VAR
    new: NameList;
  BEGIN
    IF (list = NIL) THEN
      NEW (new);
      new. next := NIL;
      new. name := name;
      list := new
    ELSIF (list. name^ # name^) THEN
      AddName (list. next, name)
    END
  END AddName;


PROCEDURE Append* (VAR list: Ref; ref: Ref);
(* Appends external reference `ref' to list.  *)
  VAR
    ptr: Ref;
  BEGIN
    ref. next := NIL;
    IF (list = NIL) THEN
      list := ref
    ELSE
      ptr := list;
      WHILE (ptr. next # NIL) DO
        ptr := ptr. next
      END;
      ptr. next := ref
    END
  END Append;

PROCEDURE AppendDep* (lib: Lib; name: D.String);
(* Add new dependence upon C library `name' to library `lib'.  Nothing is done
   if such an entry already exists.  *)
  VAR
    dep, ptr, last: Dependence;
  BEGIN
    NEW (dep);
    dep. next := NIL;
    dep. lib := GetLib (libDepRef, name^, "");
    IF (lib. depList = NIL) THEN
      lib. depList := dep
    ELSE
      ptr := lib. depList;
      last := ptr;
      WHILE (ptr # NIL) & (ptr. lib # dep. lib) DO
        last := ptr;
        ptr := ptr. next
      END;
      IF (ptr = NIL) THEN
        last. next := dep
      END
    END
  END AppendDep;

PROCEDURE AddModule* (lib: Lib; module: D.Object);
  VAR
    mid: ModuleId;
  BEGIN
    NEW (mid);
    mid. name := module. name;
    mid. magicId := module. data(D.Const). int;
    mid. next := lib. modList;
    lib. modList := mid
  END AddModule;



(* procedures ReadRefList and WriteRefList are called by SystemFlags; they read
   from resp. write to symbol files the lists of external files (C code, 
   object, library) associated with INTERFACE or FOREIGN modules *)
   
PROCEDURE ReadString* (r: BinaryRider.Reader): D.String;
  VAR
    s: D.String;
    len: LONGINT;
  BEGIN
    r. ReadNum (len);
    NEW (s, len+1);
    r. ReadBytes (s^, 0, len);
    s[len] := 0X;
    RETURN s
  END ReadString;

PROCEDURE ReadOptionNames (r: BinaryRider.Reader; VAR prefix, suffix: NameList);
  PROCEDURE ReadNameList(VAR list: NameList);
    VAR
      string: D.String;
    BEGIN
      string := ReadString (r);
      WHILE (string^ # "") DO
        AddName (list, string);
        string := ReadString (r)
      END
    END ReadNameList;
  
  BEGIN
    ReadNameList (prefix);
    ReadNameList (suffix)
  END ReadOptionNames;
      
PROCEDURE ReadRefList* (r: BinaryRider.Reader): Ref;
  VAR
    ref, list, last: Ref;
    file: File;
    lib: Lib;
    mode: LONGINT;
    name: D.String;

  PROCEDURE ReadDependence (lib: Lib);
    VAR
      str: D.String;
    BEGIN
      str := ReadString (r);
      WHILE (str^ # "") DO
        AppendDep (lib, str);
        str := ReadString (r)
      END
    END ReadDependence;

  BEGIN
    list := NIL; last := NIL;
    r. ReadNum (mode);
    WHILE (mode # noRef) DO
      CASE mode OF
      | fileRef, objRef:
        NEW (file);
        InitFile (file, SHORT (SHORT (mode)), "", "");
        file. name := ReadString (r);
        file. suffix := ReadString (r);
        ReadOptionNames (r, file. prefixOptions, file. suffixOptions);
        ref := file
      ELSE  (* mode >= libRef *)
        name := ReadString (r);
        lib := GetLib (libRef, name^, "");
        ReadDependence (lib);
        ReadOptionNames (r, lib. prefixOptions, lib. suffixOptions);
        ref := lib
      END;
      IF (last = NIL) THEN
        list := ref
      ELSE
        last. next := ref
      END;
      last := ref;
      r. ReadNum (mode);
    END;
    RETURN list
  END ReadRefList;

PROCEDURE WriteString* (w: BinaryRider.Writer; VAR str: ARRAY OF CHAR);
  VAR
    len: INTEGER;
  BEGIN
    len := Strings.Length (str);
    w. WriteNum (len);
    w. WriteBytes (str, 0, len)
  END WriteString;

PROCEDURE WriteOptionNames (w: BinaryRider.Writer; prefix, suffix: NameList);
  PROCEDURE WriteNameList (list: NameList);
    BEGIN
      WHILE (list # NIL) DO
        WriteString (w, list. name^);
        list := list. next
      END;
      WriteString (w, emptyString)
    END WriteNameList;
  
  BEGIN
    WriteNameList (prefix);
    WriteNameList (suffix)
  END WriteOptionNames;

PROCEDURE WriteRefList* (w: BinaryRider.Writer; list: Ref);
  PROCEDURE WriteDependence (depList: Dependence);
    BEGIN
      WHILE (depList # NIL) DO
        WriteString (w, depList. lib. name^);
        depList := depList. next
      END;
      WriteString (w, emptyString)
    END WriteDependence;

  BEGIN
    WHILE (list # NIL) DO
      w. WriteNum (list. mode);
      WITH list: File DO
        WriteString (w, list. name^);
        WriteString (w, list. suffix^);
        WriteOptionNames (w, list. prefixOptions, list. suffixOptions)
      | list: Lib DO
        WriteString (w, list. name^);
        WriteDependence (list. depList);
        WriteOptionNames (w, list. prefixOptions, list. suffixOptions)
      END;
      list := list. next
    END;
    w. WriteNum (noRef)
  END WriteRefList;


(* functions to read and write .Lib files *)

PROCEDURE WriteLibFile* (lib: Lib; path: ARRAY OF CHAR);
  VAR
    f: Files.File;
    w: BinaryRider.Writer;
    msg: ARRAY 256 OF CHAR;
    fileName: Parameter.Filename;
    res: Files.Result;
  
  PROCEDURE WriteDepList (w: BinaryRider.Writer; ignore: Lib);
    VAR
      lib: Ref;
      dep: Dependence;
    BEGIN
      lib := libList;
      WHILE (lib # NIL) DO
        IF (lib # ignore) THEN
          WriteString (w, lib(Lib). name^);
          WriteOptionNames (w, lib(Lib). prefixOptions, lib(Lib). suffixOptions);
          dep := lib(Lib). depList;
          WHILE (dep # NIL) DO
            WriteString (w, dep. lib. name^);
            dep := dep. next
          END;
          WriteString (w, emptyString)
        END;
        lib := lib(Lib). nextLib
      END;
      WriteString (w, emptyString)
    END WriteDepList;
  
  PROCEDURE WriteModList (w: BinaryRider.Writer; modList: ModuleId);
    VAR
      mod: ModuleId;
    BEGIN
      mod := modList;
      WHILE (mod # NIL) DO
        WriteString (w, mod. name^);
        w. WriteLInt (mod. magicId);
        mod := mod. next
      END;
      WriteString (w, emptyString)
    END WriteModList;
  
  BEGIN
    ParamPaths.GeneratePathExt (lib. name^, Config.libFileExtension, fileName);
    f := Files.Tmp (fileName, {Files.read, Files.write}, res);
    IF (f = NIL) THEN
      res. GetText (msg);
      E.FileError ("Couldn't create new symbol file `%'", fileName, msg)
    ELSE
      w := BinaryRider.ConnectWriter (f);
      (* write file header, leave empty space for magic id *)
      w. WriteBytes (libFileId, 0, 4);
      
      WriteString (w, lib. name^);
      WriteString (w, lib. version^);
      WriteString (w, path);
      WriteOptionNames (w, lib. prefixOptions, lib. suffixOptions);
      WriteDepList (w, lib);
      WriteModList (w, lib. modList);
      
      (* register and close file *)
      IF (w. res # BinaryRider.done) THEN
        w. res. GetText (msg);
        E.FileError ("Write error in file `%'", fileName, msg)
      END;
      f. Register;
      IF (f. res # Files.done) THEN
        f. res. GetText (msg);
        E.FileError ("Registering file `%' failed", fileName, msg)
      END;
      f .Close;
      IF (f. res # Files.done) THEN
        f. res. GetText (msg);
        E.FileError ("Closing file `%' failed", fileName, msg)
      END
    END
  END WriteLibFile;

PROCEDURE ReadLibFile* (lib: Lib; pos: LONGINT);
  VAR
    f: Files.File;
    r: BinaryRider.Reader;
    fileName: Parameter.Filename;
    libId: ARRAY 16 OF CHAR;
    msg: ARRAY 256 OF CHAR;
    found: BOOLEAN;
    rest: LONGINT;
    res: Files.Result;
    dummy: D.String;
  
  PROCEDURE ReadDepList (r: BinaryRider.Reader; lib: Lib);
    VAR
      name: D.String;
      depLib: Lib;
    BEGIN
      name := ReadString (r);
      WHILE (r. res = BinaryRider.done) & (name^ # "") DO
        AppendDep (lib, name);
        depLib := GetLib (libRef, name^, "");
        ReadOptionNames (r, depLib. prefixOptions, depLib. suffixOptions);
        name := ReadString (r);
        WHILE (r. res = BinaryRider.done) & (name^ # "") DO
          AppendDep (depLib, name);
          name := ReadString (r)
        END;
        name := ReadString (r)
      END
    END ReadDepList;
  
  PROCEDURE ReadModList (r: BinaryRider.Reader; lib: Lib);
    VAR
      name: D.String;
      magicId: LONGINT;
      
    PROCEDURE AddModule;
      VAR
        mid: ModuleId;
      BEGIN
        NEW (mid);
        mid. name := name;
        mid. magicId := magicId;
        mid. next := lib. modList;
        lib. modList := mid
      END AddModule;
    
    BEGIN
      name := ReadString (r);
      WHILE (r. res = BinaryRider.done) & (name^ # "") DO
        r. ReadLInt (magicId);
        AddModule;
        name := ReadString (r)
      END
    END ReadModList;
  
  BEGIN
    IF (lib. modList = NIL) THEN
      (* haven't read library summary yet; locate the file using the 
         redirection table *)
      found := ParamPaths.FindPathExt (lib. name^, Config.libFileExtension, 
                                       FALSE, fileName);
      IF found THEN
        f := Files.Old (fileName, {Files.read}, res)
      END;

      IF ~found OR (f = NIL) THEN
        E.ErrIns (pos, 514, fileName)  
        (* can't open/read symbol file of module *)
      ELSE  (* file exists, could be opened *)
        r := BinaryRider.ConnectReader (f);
        libId := "XXXX";
        r. ReadBytes (libId, 0, 4);
        IF (libId # libFileId) THEN
          E.ErrIns (pos, 515, fileName)
          (* library summary doesn't start with right key *)
          
        ELSE
          dummy := ReadString (r);
          IF (dummy^ # lib. name^) THEN
            E.ErrIns2 (pos, -602, dummy^, lib. name^)
            (* warning: symbol file imported as $1 calls itself $2 *)
          END;
          lib. version := ReadString (r);
          lib. installPath := ReadString (r);
          ReadOptionNames (r, lib. prefixOptions, lib. suffixOptions);
          ReadDepList (r, lib);
          ReadModList (r, lib);
          
          (* make sure that no more bytes follow *)
          rest := f. Length() - r. Pos();
          IF (rest # 0) THEN
            IntStr.IntToStr (rest, libId);
            E.ErrIns2 (pos, -402, libId, fileName)
            (* warning: ignoring last $1 bytes of $2 *)
          END
        END;
        IF (r. res # BinaryRider.done) THEN
          r. res. GetText (msg);
          E.FileError ("Read error in file `%'", fileName, msg)
        END;
        f. Close
      END
    END;
    lib. deferred := FALSE
  END ReadLibFile;


PROCEDURE ClearMarks*;
  VAR
    ref: Ref;
  BEGIN
    ref := libList;
    WHILE (ref # NIL) DO
      ref(Lib). mark := 0;
      ref := ref(Lib). nextLib
    END
  END ClearMarks;

PROCEDURE MarkLib* (lib: Lib; o2Lib: BOOLEAN);
  VAR
    dep: Dependence;
  BEGIN
    IF o2Lib THEN
      IF (lib. mark # 2) THEN
        lib. mark := 2;
        dep := lib. depList;
        WHILE (dep # NIL) DO
          MarkLib (dep. lib, FALSE);
          dep := dep. next
        END
      END
    ELSIF (lib. mark = 0) THEN
      lib. mark := 1
    END
  END MarkLib;

PROCEDURE SortMarkedLibraries*(): Ref;
(* Sorts all marked libraries in `libList' in such a way that all libraries
   depending on libA will appear before libA in the list.  If there is a cycle
   of dependencies the procedure will call Parameter.FatalError to write an
   error message and abort the program.  Result is a list of objects of type
   `Lib' linked with `nextRef'.  *)
  VAR
    ref, list, h: Ref;
    dep: Dependence;
  BEGIN
    (* clear dependence counters *)
    ref := libList;
    WHILE (ref # NIL) DO
      ref(Lib). counter := 0;
      ref := ref(Lib). nextLib
    END;
    
    (* update counters to reflect number of depending libs; only consider libs
       that have a non-zero mark *)
    ref := libList;
    WHILE (ref # NIL) DO
      IF (ref(Lib). mark # 0) THEN
        dep := ref(Lib). depList;
        WHILE (dep # NIL) DO
          INC (dep. lib. counter);
          dep := dep. next
        END
      END;
      ref := ref(Lib). nextLib
    END;
    
    (* sort lib list, return list linked by `nextExt' *)
    list := NIL;
    LOOP
      ref := libList;
      WHILE (ref # NIL) & 
            ((ref(Lib). mark = 0) OR (ref(Lib). counter # 0)) DO
        ref := ref(Lib). nextLib
      END;
      IF (ref = NIL) THEN
        EXIT
      ELSE
        ref. nextExt := list;
        list := ref;
        ref(Lib). mark := 0;  (* remove *)
        
        (* update counter *)
        dep := ref(Lib). depList;
        WHILE (dep # NIL) DO
          DEC (dep. lib. counter);
          dep := dep. next
        END
      END
    END;
    (* were there any cycles?  see if any marked libs are left *)
    ref := libList;
    WHILE (ref # NIL) & (ref(Lib). mark = 0) DO
      ref := ref(Lib). nextLib
    END;
    IF (ref # NIL) THEN
      Parameter.FatalError ("Cyclic dependencies in external library specification")
    END;
    
    (* revert list *)
    ref := list;
    list := NIL;
    WHILE (ref # NIL) DO
      h := ref. nextExt;
      ref. nextExt := list;
      list := ref;
      ref := h
    END;
    
    RETURN list
  END SortMarkedLibraries;


BEGIN
  libList := NIL;
  libFileId[0] := CHR (ORD ("o")+128);
  libFileId[1] := CHR (ORD ("o")+43);
  libFileId[2] := CHR (ORD ("c")-17);
  libFileId[3] := CHR (ORD ("l"));
  libFileId[4] := 0X;
  emptyString := ""
END External.
