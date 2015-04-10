MODULE Kernel [FOREIGN "C";
               LINK FILE "Kernel.c" END];

IMPORT
  SYSTEM;
  
  
TYPE
  Name* = POINTER TO ARRAY OF CHAR;
  PtrList* = POINTER TO ARRAY OF SYSTEM.PTR;
  Module* = POINTER TO ModuleDesc;
  ModuleDesc* = RECORD
    next-: Module;
    name-: Name;
    key: LONGINT;
    tdescs: SYSTEM.PTR;
    procs-: PtrList;
    (**Array of addresses of exported non-type-bound procedures.  Addresses are
       sorted lexicographically by procedure name.  Information from the symbol
       file is required to map procedure names onto indexes in this array.  *)
    vars-: PtrList;
    (**Array of addresses of exported global variables.  Addresses are
       sorted lexicographically by variable name.  Information from the symbol
       file is required to map variables names onto indexes in this array.  *)
    fingerprint-: LONGINT;
    (**Fingerprint of the module's symbol file.  *)
  END;

VAR
  modules-["_program_modules"]: Module;
  
END Kernel.
