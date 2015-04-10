MODULE Kernel [FOREIGN "C";
               LINK FILE "Kernel.c" END];

IMPORT
  SYSTEM;
  
  
TYPE
  Name* = POINTER TO ARRAY OF CHAR;
  Module* = POINTER TO ModuleDesc;
  ModuleDesc* = RECORD
    next-: Module;
    name-: Name;
    key: LONGINT;
    tdescs: SYSTEM.PTR
  END;

VAR
  modules-["_program_modules"]: Module;
  
END Kernel.
