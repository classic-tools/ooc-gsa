(* 	$Id: oo2c.Mod,v 1.47 1999/11/24 19:42:26 ooc-devel Exp $	 *)
MODULE oo2c;
(*  OO2C main module.
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

IMPORT
  Out, Filenames, Strings, Parameter, ParamOptions, ParamPaths, ParamPragmas, 
  Config, Error, Scanner, SymbolTable, ParseDecl, Make, CodeGen, FileData,
  External, Build, StdTypes, SystemFlags, StdPragmas, Allocate,
  ProgramArgs, TextRider;

CONST
  defaultOptimization = "agGlAc";
  (* this string describes the optimizations that are applied to the GSA code
     by default; for a complete list see procedure InstallOptimizers below;
     this value can be overidden with the `--opt' option or by setting the
     `optimizers' value in the config file's OPTION section *)
  enhancedOptimization = "agGlAcC1agGlAc";
  (* this string describes the optimizations that are applied to the GSA code
     whenever the `optimize' option is set (e.g. by using -O); this list 
     usually contains additional phases that take too long to be part of the
     ones applied by default, or it repeats some optimizations *)
     
VAR
  restArg, i: INTEGER;
  found: BOOLEAN;
  arg, topLevelConfig: Parameter.Filename;
  pragmas: ParamPragmas.PragmaState;

CONST
  modeCompile = 0;
  modeMake = 1;
  modeMakefile = 2;
  modeMakeLib = 3;
  modeInstallLib = 4;
  
VAR
  help: ParamOptions.BooleanOption;
  writeVersion: ParamOptions.BooleanOption;
  writeConfig: ParamOptions.BooleanOption;
  mode: ParamOptions.IntegerOption;
  makeAll: ParamOptions.BooleanOption;
  makefile: ParamOptions.StringOption;
  makefileOCRules: ParamOptions.BooleanOption;
  useLibm: ParamOptions.BooleanOption;

VAR
  allocStats: ParamOptions.BooleanOption;

  
PROCEDURE Compile (sourceFile: ARRAY OF CHAR; program: CodeGen.Program;
                   makeData: Make.Module);
  VAR
    moduleData: CodeGen.Module;
  BEGIN
    (* initialize for compile *)
    Error.Init;
    Scanner.Init (sourceFile, FALSE);    (* will abort on error *)
    SymbolTable.Init;
    
    (* parse module, `ParseDecl.Module' will call the code generation 
       procedures of the back-end (in module `CodeGen') *)
    ParseDecl.removeDeadCode := ~CodeGen.stupidCodeGen. true;
    moduleData := ParseDecl.Module (program);
    IF (makeData # NIL) & (moduleData # NIL) THEN
      IF (moduleData. obj # NIL) THEN
        (* when building a library we need the data from the compiled source,
           the stuff taken from the symbol file might miss information about
           additional external files; this isn't necessary during normal
           operation *)
        Make.UpdateModuleInfo (makeData, moduleData. obj,
                                         moduleData. symbolFileMagic)
      ELSE  (* keep old value if no new module object available *)
        Make.UpdateModuleInfo (makeData, makeData. moduleInfo,
                                         moduleData. symbolFileMagic)
      END
    END;
    
    IF (makeData # NIL) & 
       ((program = NIL) OR (program. buildLib = NIL)) THEN
      (* we are not building a library; if the symbol file says it belongs to
         a library, then this information is no longer true, because we just
         recompiled the module; fix this by removing the faulty flags *)
      EXCL (makeData. moduleInfo. beFlags, StdTypes.objInLibrary);
      EXCL (makeData. moduleInfo. beFlags, StdTypes.objLibraryMaster)
    END;
    
    (* clean up *)
    Scanner.Close;
    Error.EmitErrors (TRUE);
    ParamPragmas.Restore (pragmas)
  END Compile;

PROCEDURE RunMake (main: ARRAY OF CHAR; makeAll: BOOLEAN);
  VAR
    moduleList, mod: Make.Module;
    err, found: BOOLEAN;
    file, ext: Parameter.Filename;
    program: CodeGen.Program;
  BEGIN
    (* build file name of main module; if `main' doesn't end with the module
       extension, then append it *)
    Filenames.GetExt (main, file, ext);
    IF (ext = Config.moduleExtension) THEN
      found := ParamPaths.FindPath (main, TRUE, main);
    ELSE
      Scanner.Name2File (main);
      found := ParamPaths.FindPathExt (main, Config.moduleExtension, FALSE, main)
    END;
    
    Make.Dependencies (main, makeAll, moduleList, err);
    IF ~err THEN
      program := CodeGen.CreateProgram (NIL);
      
      Error.noerr := TRUE;
      mod := moduleList;
      WHILE Error.noerr & (mod # NIL) DO
        IF (Make.invalidSymbolFile IN mod. flags) OR
           Make.ImportChanged (mod) OR
           CodeGen.FileMissing (mod) THEN
          IF (Make.sourcesExist IN mod. flags) THEN
            ext := "- ";
            Strings.Append (mod. fileName^, ext);
            Error.VerboseMsg (ext);
            Compile (mod. fileName^, program, mod);
            INCL (mod. flags, Make.compiled)
          ELSE
            ext := "Can't find sources of module `";
            Strings.Append (mod. name^, ext);
            Strings.Append ("'", ext);
            Parameter.FatalError (ext)
          END
        ELSE
          CodeGen.AddModule (program, mod. name^)
        END;
        mod := mod. next
      END;
      
      IF Error.noerr THEN
        CodeGen.FinishProgram (program);
        Build.Executable (moduleList, "", makeAll, NIL)
      END
    END
  END RunMake;

PROCEDURE MakeLib (main: ARRAY OF CHAR);
  VAR
    moduleList, mod: Make.Module;
    err, found: BOOLEAN;
    file, ext: Parameter.Filename;
    program: CodeGen.Program;
    lib, buildLib: External.Lib;
  BEGIN
    (* build file name of main module; if `main' doesn't end with the module
       extension, then append it *)
    Filenames.GetExt (main, file, ext);
    IF (ext = Config.moduleExtension) THEN
      found := ParamPaths.FindPath (main, TRUE, main);
    ELSE
      found := ParamPaths.FindPathExt (main, Config.moduleExtension, FALSE, main)
    END;
    
    (* ugly trick; but somehow we have to make sure that we don't try to load
       the .Lib file of the library being built; otherwise we might get an 
       error saying that the .Lib of the lib we are creating doesn't exist *)
    SystemFlags.noLibFileRead := TRUE;
    Make.Dependencies (main, FALSE, moduleList, err);
    SystemFlags.noLibFileRead := FALSE;
    
    mod := moduleList;
    IF ~err THEN
      WHILE (mod. next # NIL) DO
        mod := mod. next
      END;
      IF ~(StdTypes.objLibraryMaster IN mod. moduleInfo. beFlags) THEN
        ext := "Module `";
        Strings.Append (mod. name^, ext);
        IF (StdTypes.objInLibrary IN mod. moduleInfo. beFlags) THEN
          Strings.Append ("' is already part of library `", ext);
          Strings.Append (mod. moduleInfo. beInfo(SystemFlags.Info). library. name^, ext);
          Strings.Append ("'", ext)
        ELSE
          Strings.Append ("' doesn't have a LIBRARY directive", ext)
        END;
        Parameter.FatalError (ext)
      END;
      buildLib := mod. moduleInfo. beInfo(SystemFlags.Info). library;
      program := CodeGen.CreateProgram (buildLib);
      
      (* remove all cached entries about symbol tables and libraries; this way 
         we will get the list of linked in libraries by looking at `External.
         libList' when all is done *)
      SymbolTable.importedMods := NIL;
      External.ClearLibList (buildLib);

      Error.noerr := TRUE;
      mod := moduleList;
      WHILE Error.noerr & (mod # NIL) DO
        IF (Make.usedSymFile IN mod. flags) &
           (StdTypes.objInLibrary IN mod. moduleInfo. beFlags) &
           (mod. moduleInfo. beInfo(SystemFlags.Info). library. name^ # 
             program. buildLib. name^) THEN
          (* do _not_ compile any modules taken from a different library, just
             read the library summary to get the inter library dependencies *)
          lib := mod. moduleInfo. beInfo(SystemFlags.Info). library;
          IF lib. deferred THEN
            NEW (Error.sourceFile, 11);
            COPY ("*make-lib*", Error.sourceFile^);
            StdPragmas.warnings. Set (TRUE);
            Error.Init;
            External.ReadLibFile (lib, 0)
          END
          
        ELSIF (Make.sourcesExist IN mod. flags) THEN
          ext := "- ";
          Strings.Append (mod. fileName^, ext);
          Error.VerboseMsg (ext);
          Compile (mod. fileName^, program, mod);
          IF Error.noerr THEN
            INCL (mod. flags, Make.compiled)
          END
          
        ELSE
          ext := "Can't find sources of module `";
          Strings.Append (mod. name^, ext);
          Strings.Append ("'", ext);
          Parameter.FatalError (ext)
        END;
        mod := mod. next
      END;
      
      IF Error.noerr THEN
        CodeGen.FinishProgram (program);
        (* Build.Executable will also create a summary file for the new 
           library containing all the information needed to link against it *)
        Build.Executable (moduleList, "", TRUE, program. buildLib)
      END
    END;
    
    IF (mod # moduleList) THEN
      (* remove all intermediate .c, .d, .o, and .lo file *)
      Error.VerboseMsg ("Removing intermediate files...");
      FileData.RemoveFiles;
      
      IF ~Error.noerr THEN
        (* we got an error before the library was built; remove all symbol 
           files generated in the above loop since they refer to an library
           that doesn't exist *)
        Build.RemoveSymbolFiles (moduleList)
      END
    END
  END MakeLib;

PROCEDURE InstallLib (main: ARRAY OF CHAR);
  VAR
    mod: Make.Module;
    err, found: BOOLEAN;
    file, ext: Parameter.Filename;
  BEGIN
    (* build file name of main module; if `main' doesn't end with the module
       extension, then append it *)
    Filenames.GetExt (main, file, ext);
    IF (ext = Config.moduleExtension) THEN
      found := ParamPaths.FindPath (main, TRUE, main);
    ELSE
      found := ParamPaths.FindPathExt (main, Config.moduleExtension, FALSE, main)
    END;
    
    SystemFlags.noLibFileRead := TRUE;
    mod := Make.GetModuleInfo (main, err);
    SystemFlags.noLibFileRead := FALSE;
    IF ~err THEN
      IF ~(StdTypes.objLibraryMaster IN mod. moduleInfo. beFlags) THEN
        ext := "Module `";
        Strings.Append (mod. name^, ext);
        Strings.Append ("' doesn't have a LIBRARY directive", ext);
        Parameter.FatalError (ext)
      END;
      Build.InstallLib (mod. moduleInfo. beInfo(SystemFlags.Info). library)
    END
  END InstallLib;

PROCEDURE Makefile (main, makefile: ARRAY OF CHAR);
  VAR
    moduleList: Make.Module;
    err, found: BOOLEAN;
    file, ext: Parameter.Filename;
  BEGIN
    (* build file name of main module; if `main' doesn't end with the module
       extension, then append it *)
    Filenames.GetExt (main, file, ext);
    IF (ext = Config.moduleExtension) THEN
      found := ParamPaths.FindPath (main, TRUE, main);
    ELSE
      found := ParamPaths.FindPathExt (main, Config.moduleExtension, FALSE, main)
    END;
    
    Make.Dependencies (main, FALSE, moduleList, err);
    IF ~err THEN
      Build.Makefile (moduleList, "", makefile, makefileOCRules. true)
    END
  END Makefile;

PROCEDURE WriteVersion;
  BEGIN
    Out.String (Config.defaultCompiler); Out.String ("/"); 
    Out.String (Config.defaultTargetArch); Out.String (" ");
    Out.String (Config.defaultCompilerVersion); Out.String (" for ");
    Out.String (Config.defaultTargetOS); Out.Ln
  END WriteVersion;

PROCEDURE WriteHelp;
  VAR
    argReader: TextRider.Reader;
    arg: Parameter.Filename;
  BEGIN
    argReader := TextRider.ConnectReader (ProgramArgs.args);
    argReader. ReadLine (arg);
    Out.String ("Usage:"); Out.Ln;
    Out.String ("  "); Out.String (arg); Out.String (" [options] <module>..."); Out.Ln;
    Out.String ("  "); Out.String (arg); Out.String (" (--make|-M) [options] <module>"); Out.Ln;
    Out.String ("  "); Out.String (arg); Out.String (" (--make-lib|--install-lib) [options] <module>"); Out.Ln;
    Out.String ("  "); Out.String (arg); Out.String (" --makefile <file-name> [options] <module>"); Out.Ln;
    Out.String ("Options:"); Out.Ln;
    Out.String ("  --optimize/-O, --no-rtc, --verbose/-v, --warnings/-w, --help/-h, --version, "); Out.Ln;
    Out.String ("  --config <file>, --options <string>, --pragmas <string>, --define <string>"); Out.Ln;
    Out.String ("Library Options:"); Out.Ln;
    Out.String ("  --lib-path <string>, --libtool-cmd <string>, --install-cmd <string>, "); Out.Ln;
    Out.String ("  --libtool-link"); Out.Ln;
    Out.String ("C Compiler Settings:"); Out.Ln;
    Out.String (" --cc <string>, --cflags <string>, --coptflags <string>,--ldflags <string>"); Out.Ln;
    Out.String ("  --gcflags <string>, --oc-rules"); Out.Ln;
    Out.String ("Debug Options:"); Out.Ln;
    Out.String ("  --no-build, --checks, --stupid, --translate <string>, --opt <string>,"); Out.Ln;
    Out.String ("  --gsa-qnames, --gsa-opnd-pos, --gsa-instr-pos, --gsa-assign, --gsa-gate-old,"); Out.Ln;
    Out.String ("  --cgsa, --cgsa-qnames, --cgsa-loc, --alloc-stats, --write-config"); Out.Ln;
    Out.String ("Please refer to the OOC Reference Manual for details.  The info pages should"); Out.Ln;
    Out.String ("have been installed on your system under the name `OOCref'."); Out.Ln;
  END WriteHelp;

BEGIN
  ParamPaths.Init (TRUE, TRUE, TRUE);
  ParamOptions.Init (ParamOptions.forceDefine);
  ParamPragmas.Init (ParamOptions.forceDefine);
  Parameter.include. CmdLineOption ("--include-config", "'$1'");
  
  help := ParamOptions.CreateBoolean ("help", FALSE);
  ParamOptions.options. Add (help);
  ParamOptions.options. CmdLineOption ("-h,--help", "help:=TRUE");
  writeVersion := ParamOptions.CreateBoolean ("writeVersion", FALSE);
  ParamOptions.options. Add (writeVersion);
  ParamOptions.options. CmdLineOption ("--version", "writeVersion:=TRUE");
  writeConfig := ParamOptions.CreateBoolean ("writeConfig", FALSE);
  ParamOptions.options. Add (writeConfig);
  ParamOptions.options. CmdLineOption ("--write-config", "writeConfig:=TRUE");
  
  mode := ParamOptions.CreateInteger ("mode", modeCompile, modeCompile, modeInstallLib);
  ParamOptions.options. Add (mode);
  ParamOptions.options. CmdLineOption ("-M,--make", "mode:=1");
  ParamOptions.options. CmdLineOption ("--make-lib", "mode:=3;verbose:=TRUE");
  ParamOptions.options. CmdLineOption ("--install-lib", "mode:=4;verbose:=TRUE");
  
  makeAll := ParamOptions.CreateBoolean ("makeAll", FALSE);
  ParamOptions.options. Add (makeAll);
  ParamOptions.options. CmdLineOption ("-A,--all", "makeAll:=TRUE");
  makefile := ParamOptions.CreateString ("makefile", "");
  ParamOptions.options. Add (makefile);
  ParamOptions.options. CmdLineOption ("--makefile", "mode:=2;makefile:='$1'");
  makefileOCRules := ParamOptions.CreateBoolean ("makefileOCRules", FALSE);
  ParamOptions.options. Add (makefileOCRules);
  ParamOptions.options. CmdLineOption ("--oc-rules", "makefileOCRules:=TRUE");
  
  allocStats := ParamOptions.CreateBoolean ("allocStats", FALSE);
  ParamOptions.options. Add (allocStats);
  ParamOptions.options. CmdLineOption ("--alloc-stats", "allocStats:=TRUE");
  ParamOptions.options. CmdLineOption ("--options", "$1");
  
  StdPragmas.Init;
  useLibm := ParamOptions.CreateBoolean ("TARGET_USE_LIBM", Config.defaultTargetUseLibm);
  ParamPragmas.pragmas. Add (useLibm);
  ParamPragmas.pragmas. CmdLineOption ("--pragmas", "$1");
  ParamPragmas.pragmas. CmdLineOption ("--pragmas", "$1");
  ParamPragmas.pragmas. CmdLineOption ("--define", "DEFINE $1");
  ParamPragmas.pragmas. CmdLineOption ("--no-rtc", 
    "StackCheck := FALSE; CaseSelectCheck:=FALSE; IndexCheck:=FALSE; RangeCheck:=FALSE; DerefCheck:=FALSE; FunctResult:=FALSE; TypeGuard:=FALSE; OverflowCheck:=FALSE; IntDivCheck:=FALSE; RealOverflowCheck:=FALSE; RealDivCheck:=FALSE");
  
  Parameter.ParseConfigFile (Config.defaultConfigFile, Config.configEnvVar,
                             "--config", TRUE, FALSE, topLevelConfig);
  restArg := Parameter.ParseCmdLine (TRUE, TRUE, TRUE);
  
  
  IF StdPragmas.intOverflowCheck. true THEN
    Parameter.Warning ("Runtime check `OverflowCheck' not supported, variable set to FALSE");
    StdPragmas.intOverflowCheck. Set (FALSE)
  END;
  IF (CodeGen.translationBasis. value^ = CodeGen.translateProgram) THEN
    Parameter.FatalError ("Option `--translate program' not supported (yet)");
    (* translate whole program as one large module; implies a "make all" *)
    mode. Set (modeMake);
    makeAll. Set (TRUE)
  ELSIF (CodeGen.translationBasis. value^ # CodeGen.translateGlobProc) &
        (CodeGen.translationBasis. value^ # CodeGen.translateModule) THEN
    Parameter.FatalError ("Invalid translation basis, has to be `gproc', `module', or `program'")
  END;

  IF (CodeGen.optimizers. value^ = CodeGen.useDefaultOpt) THEN
    (* no explicit optimization steps defined: assign applied optimizations 
       depending on the -O switch (i.e., the value of the `optimize' variable);
       note that optimizations explicitly specified by the user are never
       overidden *)
    IF Build.optimize. true THEN
      CodeGen.optimizers. Set (enhancedOptimization)
    ELSE
      CodeGen.optimizers. Set (defaultOptimization)
    END
  END;
  CodeGen.CheckOptimizers;
  
  IF writeConfig. true THEN
    Out.String ("# version: ");
    WriteVersion;
    Out.String ("# initialization file: ");
    Out.String (topLevelConfig);
    Out.Ln;
    Parameter.WriteConfig
  ELSIF writeVersion. true THEN
    WriteVersion
  ELSIF help. true THEN
    WriteHelp
  ELSIF (restArg = 0) THEN
    Parameter.FatalError ("Nothing to compile")
  ELSE
    (* store current pragma state in order to restore it after every 
       compilation of a module; this has to be done after all options have been
       parsed, but before the first symbol is read from the source file *)
    ParamPragmas.Save (pragmas); 
    
    IF (mode. value = modeCompile) THEN (* simple compilation *)
      i := 0;
      REPEAT
        Parameter.GetArg (i, arg);
        found := ParamPaths.FindPath (arg, FALSE, arg);
        Compile (arg, NIL, NIL);
        INC (i)
      UNTIL (i = restArg) OR ~Error.noerr
    ELSIF (restArg = 1) THEN
      Parameter.GetArg (0, arg);
      CASE mode. value OF
      | modeMake:                     (* run make *)
        RunMake (arg, makeAll. true)
      | modeMakefile:                 (* write makefile *)
        Makefile (arg, makefile. value^)
      | modeMakeLib:                  (* create shared/static library *)
        Build.CheckLibtool;
        MakeLib (arg)
      | modeInstallLib:               (* install shared/static library *)
        Build.CheckLibtool;
        InstallLib (arg)
      END
    ELSE
      Parameter.FatalError ("Too many parameters")
    END;
    
    IF ~Error.noerr THEN
      HALT (1)
    ELSIF allocStats. true THEN
      Allocate.WriteStats
    END
  END  
END oo2c.
