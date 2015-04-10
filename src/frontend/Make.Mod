(*	$Id: Make.Mod,v 1.24 1999/11/06 15:34:02 ooc-devel Exp $	*)
MODULE Make;
(*  Contructs import graph for a given main module.
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
  Strings, Files, BinaryRider, Time, Out, 
  Parameter, ParamPaths, ParamPragmas, Config, Data, Error, Scanner, 
  Sym := SymbolTable, SymbolFile, SystemFlags;

  
TYPE
  Import* = POINTER TO ImportDesc;
  Module* = POINTER TO ModuleDesc;
  
  ImportDesc* = RECORD
    next-: Import;                       (* next module in import list *)
    module-: Module;                     (* reference to module info *)
    magic: LONGINT;                      (* imported magic number *)
    hasMagic: BOOLEAN;                   (* set if `magic' is valid *)
    pos: LONGINT;                        (* position of import in source *)
  END;
  
  ModuleDesc* = RECORD
    next-: Module;                       
    (* next module in global module list *)
    name-: Data.String;
    (* name of module, or empty string if name isn't known yet *)
    fileName-: Data.String;
    (* file name of module sources, or empty string if it isn't know yet *)
    flags*: SET;
    (* see below for the possbile flag values and their meaning *)
    importList-: Import;
    (* list of imports of this module, derived from the module sources or 
       from the (up to date) symbol file *)
    moduleInfo-: Data.Object;
    (* reference to the module's symbol table entry, contains also the back-end
       dependent information *)
    magic*: LONGINT;
    (* the symbol file's magic number; only valid if `usedSymFile' is 
       set *)
    count: INTEGER;
    (* reference counter used by `TopSort' *)
  END;
  
CONST
  (* value for `ModuleDesc.flags': *)
  moduleWasScanned = 0;
  (* set if the module's import list has been read, either from the symbol file
     or from the source file itself *)
  usedSymFile* = 1;
  (* the import list was scanned from the symbol file; field `magic' is valid *)
  usedSources = 2;
  (* the import list was scanned from the source file *)
  sourcesExist* = 3;
  (* set if a file was found that may be the source text of the module *)
  invalidSymbolFile* = 4;
  (* set if the symbol file does not exist, is broken, or shouldn't be used; if
     cleared then the import list is extracted from the symbol file, otherwise
     from the sources *)
  noSuchModule = 5;
  (* set if neither the symbol file nor the source file exists *)
  marked = 6;
  (* marker for cyclic import list detection *)
  compiled* = 7;
  (* set if the module sources were translated as part of a `make'; this 
     doesn't necessarily mean that the symbol file or the module code changed,
     though *)

VAR
  (* holds the pragma state that holds before parsing of a module starts; it
     has to be stored after all options have been parsed, but before the first
     symbol is read from a source file *)
  pragmas: ParamPragmas.PragmaState;

  
PROCEDURE AddModule (VAR modList: Module; 
                     VAR moduleName, fileName: ARRAY OF CHAR): Module;
(* Add new module to module list, unless a module with the same name is already
   part of the list.  Result is the new (or old) entry.  *)
  BEGIN
    IF (modList = NIL) THEN
      NEW (modList);
      modList. next := NIL;
      NEW (modList. name, Strings.Length (moduleName)+1);
      COPY (moduleName, modList. name^);
      NEW (modList. fileName, Strings.Length (fileName)+1);
      COPY (fileName, modList. fileName^);
      modList. flags := {};
      modList. importList := NIL;
      modList. moduleInfo := NIL;
      RETURN modList
    ELSIF (modList. name^ = moduleName) THEN
      RETURN modList
    ELSE
      RETURN AddModule (modList. next, moduleName, fileName)
    END
  END AddModule;

PROCEDURE AddImport (VAR modList: Module; VAR importList: Import; 
                     VAR import: ARRAY OF CHAR; pos: LONGINT; 
                     hasMagic: BOOLEAN; magic: LONGINT);
(* Add module with name `import' to `importList', possibly creating a new entry
   in `modList'.  Nothing is done if `import' is already part of 
   `importList'.  *)
  VAR
    empty: ARRAY 2 OF CHAR;
    
  PROCEDURE SystemModule (VAR name: ARRAY OF CHAR): BOOLEAN;
  (* Returns TRUE if `name' is the name of a system module.  *)
    BEGIN
      RETURN (name = "SYSTEM")
    END SystemModule;
  
  BEGIN
    IF SystemModule (import) THEN
      (* ignore *)
    ELSIF (importList = NIL) THEN
      NEW (importList);
      importList. next := NIL;
      empty := "";
      importList. module := AddModule (modList, import, empty);
      importList. hasMagic := hasMagic;
      importList. magic := magic;
      importList. pos := pos
    ELSIF (importList. module. name^ # import) THEN
      AddImport (modList, importList. next, import, pos, hasMagic, magic)
    ELSE 
      importList. hasMagic := hasMagic;
      importList. magic := magic
    END
  END AddImport;

PROCEDURE NameMismatch (import, header: ARRAY OF CHAR);
  VAR
    msg: ARRAY 256 OF CHAR;
  BEGIN
    msg := "Module imported as `";
    Strings.Append (import, msg);
    Strings.Append ("' implements `", msg);
    Strings.Append (header, msg);
    Strings.Append ("'", msg);
    Parameter.FatalError (msg)
  END NameMismatch;

PROCEDURE ImportChanged* (mod: Module): BOOLEAN;
  VAR
    import: Import;
  BEGIN
    import := mod. importList;
    WHILE (import # NIL) DO
      IF (import. magic # import. module. magic) THEN
        RETURN TRUE
      END;
      import := import. next
    END;
    RETURN FALSE
  END ImportChanged;



PROCEDURE ScanSymbolFile (VAR moduleList: Module; f: Files.File; mod: Module);
  VAR
    r: BinaryRider.Reader;
    fileFormat, fileVersion: LONGINT;
    symId: ARRAY 5 OF CHAR;
    
  PROCEDURE ReadImportList;
    VAR
      str: Data.String;
      i, magic: LONGINT;
    BEGIN
      FOR i := 0 TO 1 DO
        LOOP
          str := SymbolFile.ReadString (r);
          IF (str^ = "") THEN
            EXIT
          END;
          r. ReadLInt (magic);
          AddImport (moduleList, mod. importList, str^, Data.undefPos, 
                     TRUE, magic)
        END
      END
    END ReadImportList;
  
  BEGIN
    r := BinaryRider.ConnectReader (f);
    symId := "XXXX";
    r. ReadBytes (symId, 0, 4);
    IF (symId # SymbolFile.symbolFileId) THEN
      INCL (mod. flags, invalidSymbolFile)
    ELSE
      mod. moduleInfo := Sym.NewModule (mod. name^, Data.undefPos);
      r. ReadLInt (mod. magic);
      mod. moduleInfo. data(Data.Const). int := mod. magic;
      
      mod. moduleInfo. name := SymbolFile.ReadString (r);
      IF (mod. name^ # mod. moduleInfo. name^) THEN
        NameMismatch (mod. name^, mod. moduleInfo. name^)
      END;
      
      (* read list of imports and import the symbol tables of the modules 
         this one is depending on *)
      ReadImportList;
      r. ReadNum (fileFormat);
      r. ReadNum (fileVersion);
      IF (fileFormat # Config.symbolFileFormat) OR
         (fileVersion # Config.symbolFileVersion) THEN
        INCL (mod. flags, invalidSymbolFile)
      ELSE
        (* read back-end specific information *)
        SymbolFile.ReadFlags (r, mod. moduleInfo. flags);
        SymbolFile.ReadFlags (r, mod. moduleInfo. beFlags);
        IF (Data.objExportsBEInfo IN mod. moduleInfo. flags) THEN
          SystemFlags.ReadObjectInfo (r, mod. moduleInfo)
        END
      END;
      
      INCL (mod. flags, usedSymFile)
    END
  END ScanSymbolFile;

PROCEDURE ScanSources (VAR moduleList: Module; mod: Module): BOOLEAN;
(* Reads the import list from the sources of `mod'.  Result is `TRUE' if no
   syntax error occured.  *)
    
  PROCEDURE ImportList;
  (* Parses list of module imports and adds them to `mod. importList' *)
    VAR
      pos: LONGINT;
      modId: ARRAY 1024 OF CHAR;
      
    PROCEDURE GetModuleIdent;
      BEGIN
        Scanner.moduleIdent := TRUE;
        Scanner.GetSym;
        Scanner.moduleIdent := FALSE
      END GetModuleIdent;
    
    BEGIN  (* pre: Scanner.sym = import *)
      GetModuleIdent;
      LOOP
        IF (Scanner.sym = Scanner.ident) THEN
          COPY (Scanner.str^, modId);
          pos := Scanner.currSymPos;
          Scanner.GetSym;
          IF (Scanner.sym = Scanner.becomes) THEN
            GetModuleIdent;
            IF (Scanner.sym = Scanner.ident) THEN
              COPY (Scanner.str^, modId);
              pos := Scanner.currSymPos;
              Scanner.GetSym
            ELSE
              Error.Err (Scanner.currSymPos, 100)  (* identifier expected *)
            END
          END;
          IF (modId = mod. name^) THEN
            Error.Err (pos, 306)             (* module can't import itself *)
          ELSE
            AddImport (moduleList, mod. importList, modId, pos, FALSE, 0)
          END
        ELSE
          Error.Err (Scanner.currSymPos, 100)  (* identifier expected *)
        END;
        IF (Scanner.sym # Scanner.comma) THEN
          EXIT
        END;
        GetModuleIdent
      END;
      Scanner.CheckSym (Scanner.semicolon)
    END ImportList;
    
  BEGIN
    (* initialize for compile *)
    Error.Init;
    Scanner.Init (mod. fileName^, TRUE); (* will abort on error *)
    (* the scanner might have checked out the file from a version control's 
       master file; compare `mod.fileName^' against the true name stored in
       `Error.sourceFile^'; if they differ discard the name of the master file
       and use the working file instead *)
    IF (mod. fileName^ # Error.sourceFile^) THEN
      NEW (mod. fileName, Strings.Length (Error.sourceFile^)+1);
      COPY (Error.sourceFile^, mod. fileName^)
    END;
    Sym.Init;
    
    (* parse module header *)
    Scanner.moduleIdent := TRUE;
    Scanner.CheckSym (Scanner.module);
    Scanner.moduleIdent := FALSE;
    IF Error.noerr THEN
      IF (Scanner.sym = Scanner.ident) THEN
        IF (mod. name^ = "") THEN  (* fill in module name from source file *)
          NEW (mod. name, Strings.Length (Scanner.str^)+1);
          COPY (Scanner.str^, mod. name^)
        ELSIF (mod. name^ # Scanner.str^) THEN
          (* compare module name with the header in the file *)
          NameMismatch (mod. name^, Scanner.str^)
        END;
        
        (* create root of symbol table *)
        mod. moduleInfo := Sym.NewModule (Scanner.str^, Scanner.currSymPos);
        Sym.OpenScope (mod. moduleInfo, Sym.currentModuleId, Sym.globalLevel);
        Scanner.GetSym;
        SystemFlags.ObjectModifiers (mod. moduleInfo, TRUE);
        
        (* parse import list *)
        Scanner.CheckSym (Scanner.semicolon);
        IF (Scanner.sym = Scanner.import) THEN
          ImportList
        END;
        
        (* stop parsing, clean up *)
        Sym.CloseScope (Error.noerr);
        SystemFlags.ObjectModifiers (mod. moduleInfo, FALSE);
        INCL (mod. flags, usedSources)
      ELSE
        Error.Err (Scanner.currSymPos, 100)  (* identifier expected *)
      END
    END;
    
    (* clean up *)
    Scanner.Close;
    Error.EmitErrors (FALSE);
    RETURN Error.noerr
  END ScanSources;

PROCEDURE ScanModule (VAR moduleList: Module; mod: Module; 
                      useSources: BOOLEAN): BOOLEAN;
(* Scans the imports of `mod' and adds them to `mod. importList'.  If possible
   the imports are taken from the symbol file, otherwise from the source file.
   The latter case is used with `useSource=TRUE'.  Result is `TRUE' if no 
   syntax errors were found.  *)
  VAR
    foundSources, foundSym, ok: BOOLEAN;
    res: Files.Result;
    fileName: Parameter.Filename;
    symFile: Files.File;
    sourceStamp, lastCompilation: Time.TimeStamp;
    
  BEGIN
    (* if the module's file name hasn't been set yet, then let ParamPaths
       find one for us *)
    IF (mod. fileName^ = "") THEN
      COPY (mod. name^, fileName);
      Scanner.Name2File (fileName);
      foundSources := ParamPaths.FindPathExt (fileName, Config.moduleExtension,
                                              FALSE, fileName);
      IF foundSources THEN
        NEW (mod. fileName, Strings.Length (fileName)+1);
        COPY (fileName, mod. fileName^)
      END
    ELSE
      foundSources := Files.Exists (mod. fileName^)
    END;
    IF foundSources THEN
      INCL (mod. flags, sourcesExist)
    END;
    
    (* check if the import list of the symbol file can be used *)
    symFile := NIL;
    IF (mod. name^ # "") & (~useSources OR ~foundSources) THEN
      (* build name of symbol file *)
      foundSym := ParamPaths.FindPathExt (mod. name^, Config.symbolExtension, 
                                          FALSE, fileName);
      IF foundSym THEN 
        (* compare time stamp with source file *)
        Files.GetModTime (fileName, lastCompilation, res);
        IF (res = Files.done) THEN
          IF foundSources THEN
            (* check if the sources are more recent than the symbol file *)
            Files.GetModTime (mod. fileName^, sourceStamp, res);
            IF (res = Files.done) & 
               (lastCompilation. Cmp (sourceStamp) > 0) THEN
              symFile := Files.Old (fileName, {Files.read}, res)
            END
          ELSE
            symFile := Files.Old (fileName, {Files.read}, res)
          END
        END
      END
    END;
    
    ok := TRUE;
    IF (symFile # NIL) THEN              (* scan symbol file *)
      ScanSymbolFile (moduleList, symFile, mod);
      symFile. Close
    ELSIF (mod. name^ = "") OR foundSources THEN (* scan source file *)
      INCL (mod. flags, invalidSymbolFile);
      ok := ScanSources (moduleList, mod)
    ELSE
      INCL (mod. flags, noSuchModule)
    END;
    
    INCL (mod. flags, moduleWasScanned);
    ParamPragmas.Restore (pragmas);
    RETURN ok
  END ScanModule;


PROCEDURE TopSort (modules: Module; mainFirst: BOOLEAN): Module;
(* Does a topological sort on the list of modules.
   pre: `modules' is a list of modules, each of it contains a list of all its 
     imported modules in `module.importList'.
   post: Result is a permutation of the list `modules' in such a way, that
     each module precedes all other modules in the list that are importing it. 
     `mainFirst' determines if the main module should be at the head of the 
     list (TRUE) or whether the list should be reversed (FALSE). 
   If a cyclic import exits, then the program aborts with an error message.  *)
  VAR
    mod: Module;
    inode: Import;
    topList: Module;
    msg: ARRAY 8*1024 OF CHAR;
  
  PROCEDURE RemoveBest (VAR mod: Module; prevBest: INTEGER): Module;
  (* pre: `mod' contains the unsearched part of the module list, `prevBest' 
       the minimum import count encountered in the list til node `mod'.
     post: If the list starting at `mod' contains a module whose module count 
       is below `prevBest', this module is removed from the list and returned 
       as the result.  Otherwise NIL is returned and the list is not modified. *)
    VAR
      best: Module; 
    BEGIN
      IF (mod = NIL) THEN
        RETURN NIL
      ELSIF (mod. count < prevBest) THEN
        best := RemoveBest (modules. next, mod. count);
        IF (best = NIL) THEN
          best := mod;
          mod := mod. next
        END;
        RETURN best
      ELSE
        RETURN RemoveBest (mod. next, prevBest)
      END
    END RemoveBest;
      
  PROCEDURE ErrorCyclic (mod: Module);
    VAR
      len: INTEGER;
      import: Import;
    BEGIN
      IF (mod. count # 0) THEN
        len := Strings.Length (msg);
        IF (marked IN mod. flags) THEN
          Parameter.FatalError (msg)
        ELSE
          INCL (mod. flags, marked);
          Strings.Append (" ", msg);
          Strings.Append (mod. name^, msg);
          import := mod. importList;
          WHILE (import # NIL) DO
            ErrorCyclic (import. module);
            import := import. next
          END;
          EXCL (mod. flags, marked);
          msg[len] := 0X
        END
      END
    END ErrorCyclic;
  
  BEGIN
    (* initialize import counter for each module *)
    mod := modules;
    WHILE (mod # NIL) DO
      mod. count := 0;
      inode := mod. importList;
      WHILE (inode # NIL) DO
        INC (mod. count);
        inode := inode. next
      END;
      mod := mod. next
    END;
    
    (* rearrange list in `modules', store result in `topList' *)
    topList := NIL;
    WHILE (modules # NIL) DO
      mod := RemoveBest (modules, MAX(INTEGER));
      mod. next := topList;
      topList := mod;
      IF (topList. count # 0) THEN  (* oops, cyclic import *)
        msg := "Cyclic import via";
        ErrorCyclic (topList)
      END;
      
      (* update import count in remaining modules *)
      mod := modules;
      WHILE (mod # NIL) DO
        inode := mod. importList;
        WHILE (inode # NIL) DO
          IF (inode. module = topList) THEN
            DEC (mod. count)
          END;
          inode := inode. next
        END;
        mod := mod. next
      END
    END;
    
    IF mainFirst THEN
      RETURN topList
    ELSE
      (* revert `topList' in order to move the module with the least imports 
         to the start *)
      WHILE (topList # NIL) DO
        mod := topList;
        topList := topList. next;
        mod. next := modules;
        modules := mod
      END;
      RETURN modules
    END
  END TopSort;
    

PROCEDURE Dependencies* (fileName: ARRAY OF CHAR; useSources: BOOLEAN;
                         VAR modList: Module; VAR err: BOOLEAN);
(* Given `fileName' as the file name of the main module, determine all modules
   it is depending on and construct the dependence graph of their import
   relationship.  *)
  VAR
    ok: BOOLEAN;
    empty: ARRAY 2 OF CHAR;
    main, mod: Module;
  
  PROCEDURE ImportsUnknown (mod: Module): BOOLEAN;
    VAR
      import: Import;
    BEGIN
      import := mod. importList;
      WHILE (import # NIL) DO
        IF (noSuchModule IN import. module. flags) THEN
          RETURN TRUE
        END;
        import := import. next
      END;
      RETURN FALSE
    END ImportsUnknown;
  
  PROCEDURE MarkUnknownImports (mod: Module; useError: BOOLEAN);
    VAR
      import: Import;
    BEGIN
      import := mod. importList;
      WHILE (import # NIL) DO
        IF (noSuchModule IN import. module. flags) THEN
          IF useError THEN
            Error.ErrIns (import. pos, 307, import. module. name^)
          ELSE
            Out.String ("Error: Module `"); 
            Out.String (mod. name^);
            Out.String ("' imports unknown module `");
            Out.String (import. module. name^);
            Out.Char ("'");
            Out.Ln
          END
        END;
        import := import. next
      END
    END MarkUnknownImports;
  
  BEGIN
    ParamPragmas.Save (pragmas);
    modList := NIL;
    empty := "";
    main := AddModule (modList, empty, fileName);
    (* first scan reads the module name from the file `main' *)
    ok := ScanModule (modList, main, useSources);
    IF ok & ~useSources THEN  
      (* second scan reads the symbol file to get the magic numbers *)
      EXCL (main. flags, invalidSymbolFile);
      ok := ScanModule (modList, main, FALSE)
    END;
    
    IF ok THEN
      (* iterate over module list until all modules are scanned in *)
      REPEAT
        mod := modList;
        WHILE (mod # NIL) & (moduleWasScanned IN mod. flags) DO
          mod := mod. next
        END;
        IF (mod # NIL) THEN
          ok := ScanModule (modList, mod, useSources)
        END
      UNTIL (mod = NIL) OR ~ok
    END;
    
    IF ok THEN
      (* check for every module if it imports unknown modules; any such import
         is marked with an error message *)
      mod := modList;
      WHILE (mod # NIL) DO
        IF ImportsUnknown (mod) THEN
          ok := FALSE;
          IF ~(usedSources IN mod. flags) & 
             (sourcesExist IN mod. flags) THEN
            ok := ScanModule (modList, mod, TRUE);
            ok := FALSE
          END;
          IF (usedSources IN mod. flags) THEN
            Error.Init;
            Error.sourceFile := mod. fileName;
            MarkUnknownImports (mod, TRUE);
            Error.EmitErrors (FALSE)
          ELSE
            MarkUnknownImports (mod, FALSE)
          END
        END;
        mod := mod. next
      END;

      IF ok THEN
        (* topological sort on modules *)
        modList := TopSort (modList, FALSE)
      END
    END;
    err := ~ok
  END Dependencies;

PROCEDURE GetModuleInfo* (fileName: ARRAY OF CHAR; VAR err: BOOLEAN): Module;
(* Retrieves back-end specific information associated with the given module.
   This information is taken from the beginning of the symbol file (if
   available), or from the module's source code otherwise.  *)
  VAR
    empty: ARRAY 2 OF CHAR;
    main, modList: Module;
  BEGIN
    ParamPragmas.Save (pragmas);
    empty := "";
    modList := NIL;
    main := AddModule (modList, empty, fileName);
    err := ~ScanModule (modList, main, FALSE);
    RETURN main
  END GetModuleInfo;

PROCEDURE UpdateModuleInfo* (mod: Module; obj: Data.Object; magic: LONGINT);
  BEGIN
    mod. moduleInfo := obj;
    mod. magic := magic
  END UpdateModuleInfo;

END Make.
