(*	$Id: CNModules.Mod,v 1.6 1999/08/08 18:31:41 acken Exp $	*)
MODULE CNModules;
(*  Manages module lists and retrieves import information.
    Copyright (C) 1998, 1999  Michael van Acken

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
  Filenames, Strings, ParamPaths, Config, 
  Output := CNOutput, S := CNScanner;

TYPE
  Module* = POINTER TO ModuleDesc;
  ModuleList* = POINTER TO ModuleListDesc;
  ModuleListDesc = RECORD
    next-, prev-: ModuleList;
    module-: Module
  END;
  ModuleDesc = RECORD
    name-: S.String;
    importList: ModuleList;
    importNames: S.Symbol;
    count: LONGINT;
  END;




PROCEDURE Find* (modList: ModuleList; VAR name: ARRAY OF CHAR): Module;
(* Searches for module `name' in list `modList'.  If a matching module is
   found this module is returned, otherwise result is NIL.  *)
  BEGIN
    WHILE (modList # NIL) & (modList. module. name^ # name) DO
      modList := modList. next
    END;
    IF (modList = NIL) THEN
      RETURN NIL
    ELSE
      RETURN modList. module
    END
  END Find;

PROCEDURE Append (VAR modList: ModuleList; module: Module): Module;
  VAR
    new, ptr: ModuleList;
  BEGIN
    NEW (new);
    new. module := module;
    new. prev := NIL;
    new. next := NIL;
    IF (modList = NIL) THEN
      modList := new
    ELSE
      ptr := modList;
      WHILE (ptr. next # NIL) DO
        ptr := ptr. next
      END;
      new. prev := ptr;
      ptr. next := new
    END;
    RETURN module
  END Append;

PROCEDURE Insert* (VAR modList: ModuleList; VAR name: ARRAY OF CHAR): Module;
(* If a module `name' is already part of the list, a pointer to this module
   is returned.  Otherwise a new module is created and appended to the list.
   In this case the result is the newly created module.  *)
  VAR
    module: Module;
  
  PROCEDURE NewModule (VAR name: ARRAY OF CHAR): Module;
    VAR
      module: Module;
    BEGIN
      NEW (module);
      module. importList := NIL;
      module. importNames := NIL;
      NEW (module. name, Strings.Length (name)+1);
      COPY (name, module. name^);
      module. count := -1;
      RETURN module
    END NewModule;
  
  BEGIN
    module := Find (modList, name);
    IF (module # NIL) THEN
      RETURN module
    ELSE
      RETURN Append (modList, NewModule (name))
    END
  END Insert;

PROCEDURE Remove (VAR modList: ModuleList; VAR name: ARRAY OF CHAR);
(* Removes module `name' from the list.  
   pre: `name' is member of `modList'.  *)
  VAR
    ptr: ModuleList;
  BEGIN
    ptr := modList;
    WHILE (ptr. module. name^ # name) DO
      ptr := ptr. next
    END;
    IF (ptr. next # NIL) THEN
      ptr. next. prev := ptr. prev
    END;
    IF (ptr. prev # NIL) THEN
      ptr. prev. next := ptr. next
    END;
    IF (modList = ptr) THEN
      modList := modList. next
    END
  END Remove;



PROCEDURE LocateModule* (name: ARRAY OF CHAR; VAR filename: ARRAY OF CHAR);
(* Given the name of a module, determine the file name of the module's source
   code.  *)
  VAR
    file, ext: S.Filename;
    found: BOOLEAN;
    i: INTEGER;
  BEGIN
    i := 0;
    WHILE (name[i] # 0X) DO
      IF (name[i] = S.moduleSeparator) THEN
        name[i] := "/"
      END;
      INC (i)
    END;
    
    (* build file name of name module; if `name' doesn't end with the module
       extension simply append it *)
    Filenames.GetExt (name, file, ext);
    IF (ext = Config.moduleExtension) THEN
      found := ParamPaths.FindPath (name, TRUE, file)
    ELSE
      found := ParamPaths.FindPathExt (name, Config.moduleExtension, FALSE, file)
    END;
    COPY (file, filename)
  END LocateModule;

PROCEDURE InternalModule* (name: ARRAY OF CHAR): BOOLEAN;
  BEGIN
    RETURN (name = "SYSTEM")
  END InternalModule;

PROCEDURE ScanModule (module: Module; noInternal: BOOLEAN);
(* Scans import list of `module' and stores it in `module. importNames'.  The
   first element of this list is the name of the module itself, followed by
   the names of the imported modules.  If `noInternal=TRUE', all references to
   internal modules like "SYSTEM" are removed from the import list.  *)
  VAR
    file: S.Filename;
    sym, next: S.Symbol;
  BEGIN
    IF InternalModule (module. name^) THEN
      module. importNames := S.undefSym
    ELSE
      LocateModule (module. name^, file);
      module. importNames := S.ScanImports (file);
      
      IF noInternal THEN  (* remove imported internal modules *)
        sym := module. importNames;
        WHILE (sym # NIL) DO
          next := sym. next;
          IF InternalModule (sym. str^) THEN
            sym. Remove
          END;
          sym := next
        END
      END
    END
  END ScanModule;

PROCEDURE TopSort (modList: ModuleList): ModuleList;
(* Do a topological sort on `modList' based on the import relationship.  *)
  VAR
    newList, ptr, best, import: ModuleList;
    mod, dummy: Module;
  BEGIN
    newList := NIL;
    
    ptr := modList;
    WHILE (ptr # NIL) DO
      mod := ptr. module;
      mod. count := 0;
      import := mod. importList;
      WHILE (import # NIL) DO
        INC (mod. count);
        import := import. next
      END;
      ptr := ptr. next
    END;
    
    WHILE (modList # NIL) DO
      best := NIL;
      ptr := modList;
      WHILE (ptr # NIL) DO
        IF (ptr. module. count = 0) THEN
          best := ptr
        END;
        ptr := ptr. next
      END;
      IF (best = NIL) THEN
        Output.FatalError ("Cyclic import")
      ELSE
        Remove (modList, best. module. name^);
        dummy := Insert (newList, best. module. name^);
        
        ptr := modList;
        WHILE (ptr # NIL) DO
          import := ptr. module. importList;
          WHILE (import # NIL) DO
            IF (import. module = best. module) THEN
              DEC (ptr. module. count)
            END;
            import := import. next
          END;
          ptr := ptr. next
        END
      END
    END;
    
    RETURN newList
  END TopSort;


PROCEDURE Closure* (VAR modList: ModuleList; noInternal: BOOLEAN);
(* Extend the module list `modList' to include all modules imported directly or
   indirectly by elements of `modList'.  Afterwards any module appearing in one
   of the import statement in `modList' will also be part of `modList'.  If 
   `noInternal=TRUE', imports of internal modules like "SYSTEM" are ignored. *)
  VAR
    curr: ModuleList;
    mod: Module;
    import: S.Symbol;
    module: Module;
  BEGIN
    curr := modList;
    WHILE (curr # NIL) DO
      mod := curr. module;
      IF (mod. importNames = NIL) THEN
        ScanModule (mod, noInternal);
        import := mod. importNames. next;
        WHILE (import # NIL) DO
          module := Append (mod. importList, Insert (modList, import. str^));
          import := import. next
        END
      END;
      curr := curr. next
    END;
    
    modList := TopSort (modList)
  END Closure;

END CNModules.
