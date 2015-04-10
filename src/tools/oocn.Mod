(*	$Id: oocn.Mod,v 1.19 1999/12/07 11:44:19 ooc-devel Exp $	*)
MODULE oocn;
(*  Main module of the OOC Code Navigator toolbox.
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
  ProgramArgs, Channel, TextRider, Filenames, Out, Files,
  Parameter, ParamPaths, ParamOptions, ParamPragmas, StdPragmas,
  Config, S := CNScanner, AST := CNAST, Parser := CNParser, Filter := CNFilter,
  Modules := CNModules, Decl := CNDecl, HTML := CNHTML, Text := CNText,
  XRef := CNXRef, ModuleDef := CNModuleDef, Output := CNOutput, 
  DefTexi := CNDefTexi, ScanFile := CNScanFile;

VAR
  topLevelConfig: S.Filename;
  restArg: INTEGER;

CONST
  modeHelp = 0;
  modeHTML = 1;
  modeXRef = 2;
  modeModules = 3;
  modeListUses = 4;
  modeInterface = 5;
  modeFilter = 6;
  
  mdefText = 0;
  mdefHTML = 1;
  mdefXRef = 2;
  mdefTexi = 3;
  
VAR
  writeVersion: ParamOptions.BooleanOption;
  writeConfig: ParamOptions.BooleanOption;
  mode: ParamOptions.IntegerOption;
  modeDef: ParamOptions.IntegerOption;
  closure: ParamOptions.BooleanOption;
  noInternal: ParamOptions.BooleanOption;
  lineNum: ParamOptions.BooleanOption;
  colorSet: ParamOptions.StringOption;
  declName: ParamOptions.StringOption;
  moduleArgs: Modules.ModuleList;

  filterOptions: Filter.Set;

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
    arg: S.Filename;
  BEGIN
    Out.String ("Usage: ");
    argReader := TextRider.ConnectReader (ProgramArgs.args);
    argReader. ReadLine (arg);
    Out.String (arg);
    Out.String (" <mode> [options] <module>..."); Out.Ln;
    Out.String ("Modes:"); Out.Ln;
    Out.String ("  --html,-H       Translate listed modules into HTML code."); Out.Ln;
    Out.String ("  --xref,-X       Create cross-reference tables in HTML format."); Out.Ln;
    Out.String ("  --uses <decl>,-U <decl>"); Out.Ln;
    Out.String ("                  List all uses of the given declaration."); Out.Ln;
    Out.String ("  --modules,-M    List all imported modules."); Out.Ln;
    Out.String ("  -d              Write interface of modules to stdout."); Out.Ln;
    Out.String ("  --def-txt, --def-html, --def-xref, --def-texi"); Out.Ln;
    Out.String ("                  Produce module definitions in different output formats."); Out.Ln;
    Out.String ("  --filter,-F     Filter module source text."); Out.Ln;
    Out.String ("Options:"); Out.Ln;
    Out.String ("  --closure,-C    Operate on all modules imported by set of root modules."); Out.Ln;
    Out.String ("  --no-internal   Omit internal modules from the output of --modules."); Out.Ln;
    Out.String ("  --line-num      Prepend original line number to every line of output."); Out.Ln;
    Out.String ("  --strip-comments,--strip-doc-strings,--strip-pragmas,--strip-system-flags,"); Out.Ln;
    Out.String ("  --strip-mp-ident"); Out.Ln;
    Out.String ("                  Remove or rewrite tokens from the module's source text."); Out.Ln;
    Out.String ("  --mod2foreign, --foreign2mod"); Out.Ln;
    Out.String ("                  Convert module to FOREIGN and back (options for --filter)."); Out.Ln;
    Out.String ("  --colors <name> Select color set used for HTML.  Available:"); Out.Ln;
    Out.String ("                      hilit (default), font-lock"); Out.Ln;
    Out.String ("  -o <dir>        Change output directory for generated files; - means stdout."); Out.Ln;
    Out.String ("  -v              Verbose mode."); Out.Ln;
    Out.String ("  --version       Write program version to stdout and exit."); Out.Ln;
    Out.String ("  --help,-h       Write this text to stdout and exits."); Out.Ln;
  END WriteHelp;


PROCEDURE WriteHTML (modList: Modules.ModuleList; filter: Filter.Set);
  PROCEDURE ConvertModule (VAR name: ARRAY OF CHAR);
    VAR
      list: S.StartSymbol;
      module: AST.Module;
      filename: S.Filename;
      ch: Channel.Channel;
    BEGIN
      Modules.LocateModule (name, filename);
      list := ScanFile.Scan (filename);
      S.Abs2Rel (list);
      module := Parser.ParseModule (list);
      Filter.Apply (module. startSymbol, filter);
      
      ch := Output.Open (module. name. name. str^, "", "html");
      HTML.SetWriter (TextRider.ConnectWriter (ch));
      HTML.WriteSymbols (module, "", FALSE, lineNum. true);
      Output.Close (ch);
      
      Decl.RemoveLocal (module);
      Decl.CacheModule (module);
      S.ClearStringTable
    END ConvertModule;
  
  BEGIN
    HTML.SetColors (colorSet. value^);
    Decl.FlushCache;
    WHILE (modList # NIL) DO
      IF ~Modules.InternalModule (modList. module. name^) THEN
        ConvertModule (modList. module. name^)
      END;
      modList := modList. next
    END
  END WriteHTML;

PROCEDURE WriteText (modList: Modules.ModuleList; filter: Filter.Set);
  PROCEDURE ConvertModule (VAR name: ARRAY OF CHAR);
    VAR
      list: S.StartSymbol;
      module: AST.Module;
      filename: S.Filename;
      ch: Channel.Channel;
    BEGIN
      Modules.LocateModule (name, filename);
      list := ScanFile.Scan (filename);
      S.Abs2Rel (list);
      module := Parser.ParseModule (list);
      Filter.Apply (module. startSymbol, filter);
      
      ch := Output.Open (module. name. name. str^, "", "txt");
      Text.SetWriter (TextRider.ConnectWriter (ch));
      Text.WriteSymbols (module, module. startSymbol, FALSE, lineNum. true);
      Output.Close (ch);
      
      AST.RemoveAST (module);
      S.ClearStringTable
    END ConvertModule;
  
  BEGIN
    WHILE (modList # NIL) DO
      IF ~Modules.InternalModule (modList. module. name^) THEN
        ConvertModule (modList. module. name^)
      END;
      modList := modList. next
    END
  END WriteText;

PROCEDURE WriteDefinition (modList: Modules.ModuleList; filter: Filter.Set);
  PROCEDURE ConvertModule (VAR name: ARRAY OF CHAR);
    VAR
      list: S.StartSymbol;
      module: AST.Module;
      filename: S.Filename;
      ch: Channel.Channel;
    BEGIN
      Modules.LocateModule (name, filename);
      list := ScanFile.Scan (filename);
      S.Abs2Rel (list);
      module := Parser.ParseModule (list);
      Filter.Apply (module. startSymbol, filter);
      ModuleDef.Extract (module);
      
      CASE modeDef. value OF
      | mdefText:
        ch := Output.Open (module. name. name. str^, "_def", "txt");
        Text.SetWriter (TextRider.ConnectWriter (ch));
        Text.WriteSymbols (module, list, FALSE, lineNum. true);
      | mdefHTML:
        ch := Output.Open (module. name. name. str^, "_def", "html");
        HTML.SetWriter (TextRider.ConnectWriter (ch));
        HTML.SetColors (colorSet. value^);
        HTML.WriteSymbols (module, "_def", FALSE, lineNum. true)
      | mdefTexi:
        ch := Output.Open (module. name. name. str^, "_def", "texi");
        DefTexi.SetWriter (TextRider.ConnectWriter (ch));
        DefTexi.WriteDeclarations (module)
      
      (* mdefXRef: handled separately in module body *)
      END;
      Output.Close (ch);
      
      IF (modeDef. value = mdefText) THEN
        module. Remove
      ELSE
        S.RemoveComments (module. startSymbol);
        Decl.CacheModule (module)
      END;
      S.ClearStringTable
    END ConvertModule;
  
  BEGIN
    Decl.FlushCache;
    WHILE (modList # NIL) DO
      IF ~Modules.InternalModule (modList. module. name^) THEN
        ConvertModule (modList. module. name^)
      END;
      modList := modList. next
    END
  END WriteDefinition;

PROCEDURE WriteModules (modList: Modules.ModuleList);
  BEGIN
    WHILE (modList # NIL) DO
      Out.String (modList. module. name^);
      Out.Ln;
      modList := modList. next
    END
  END WriteModules;

PROCEDURE ModuleArguments (restArg: INTEGER): Modules.ModuleList;
  VAR
    modList: Modules.ModuleList;
    dummy: Modules.Module;
    i: INTEGER;
    arg, file, ext: S.Filename;
    imports: S.Symbol;
  BEGIN
    IF (restArg = 0) THEN
      Output.FatalError ("No module arguments");
      RETURN NIL
    ELSE
      modList := NIL;
      FOR i := 0 TO restArg-1 DO
        Parameter.GetArg (i, arg);
        Filenames.GetExt (arg, file, ext);
        IF (ext = Config.moduleExtension) & Files.Exists (arg) THEN
          imports := S.ScanImports (arg);
          dummy := Modules.Insert (modList, imports. str^)
        ELSE
          Filenames.GetFile (arg, arg);
          dummy := Modules.Insert (modList, arg)
        END
      END;
      RETURN modList
    END
  END ModuleArguments;

BEGIN
  ParamPaths.Init (TRUE, TRUE, TRUE);
  ParamOptions.Init (ParamOptions.acceptUndef);
  ParamPragmas.Init (ParamOptions.forceDefine);
  Parameter.include. CmdLineOption ("--include-config", "'$1'");

  StdPragmas.Init;
  ParamOptions.options. CmdLineOption ("--options", "$1");
  ParamPragmas.pragmas. CmdLineOption ("--pragmas", "$1");
  
  writeVersion := ParamOptions.CreateBoolean ("writeVersion", FALSE);
  ParamOptions.options. Add (writeVersion);
  ParamOptions.options. CmdLineOption ("--version", "writeVersion:=TRUE");
  writeConfig := ParamOptions.CreateBoolean ("writeConfig", FALSE);
  ParamOptions.options. Add (writeConfig);
  ParamOptions.options. CmdLineOption ("--write-config", "writeConfig:=TRUE");

  mode := ParamOptions.CreateInteger ("mode", modeHelp, modeHelp, modeFilter);
  ParamOptions.options. Add (mode);
  declName := ParamOptions.CreateString ("declName", "");
  ParamOptions.options. Add (declName);
  ParamOptions.options. CmdLineOption ("--help,-h", "mode:=0");
  ParamOptions.options. CmdLineOption ("--html,-H", "mode:=1");
  ParamOptions.options. CmdLineOption ("--xref,-X", "mode:=2;closure:=TRUE");
  ParamOptions.options. CmdLineOption ("--modules,-M", "mode:=3;closure:=TRUE;parseTexinfo:=FALSE");
  ParamOptions.options. CmdLineOption ("--uses,-U", "mode:=4;declName:='$1';closure:=TRUE;parseTexinfo:=FALSE");
(*  ParamOptions.options. CmdLineOption ("--definition,-D", "mode:=5");*)
  ParamOptions.options. CmdLineOption ("--filter,-F", "mode:=6;parseTexinfo:=FALSE");

  modeDef := ParamOptions.CreateInteger ("modeDef", mdefText, mdefText, mdefTexi);
  ParamOptions.options. Add (modeDef);
  ParamOptions.options. CmdLineOption ("--def-txt", "mode:=5;modeDef:=0");
  ParamOptions.options. CmdLineOption ("--def-html", "mode:=5;modeDef:=1");
  ParamOptions.options. CmdLineOption ("--def-xref", "mode:=5;modeDef:=2");
  ParamOptions.options. CmdLineOption ("--def-texi", "mode:=5;modeDef:=3");
  ParamOptions.options. CmdLineOption ("-d", "mode:=5;modeDef:=0;outputDir:='-'");

  closure := ParamOptions.CreateBoolean ("closure", FALSE);
  ParamOptions.options. Add (closure);
  ParamOptions.options. CmdLineOption ("--closure,-C", "closure:=TRUE");
  
  noInternal := ParamOptions.CreateBoolean ("noInternal", FALSE);
  ParamOptions.options. Add (noInternal);
  ParamOptions.options. CmdLineOption ("--no-internal", "noInternal:=TRUE");
    
  lineNum := ParamOptions.CreateBoolean ("lineNumbers", FALSE);
  ParamOptions.options. Add (lineNum);
  ParamOptions.options. CmdLineOption ("--line-num", "lineNumbers:=TRUE");
  
  colorSet := ParamOptions.CreateString ("colorSet", "hilit19");
  ParamOptions.options. Add (colorSet);
  ParamOptions.options. CmdLineOption ("--colors", "colorSet:='$1'");
  
  
  Parameter.ParseConfigFile (Config.defaultConfigFile, Config.configEnvVar,
                             "--config", TRUE, TRUE, topLevelConfig);
  restArg := Parameter.ParseCmdLine (TRUE, TRUE, TRUE);
  
  ParamPragmas.Save (S.pragmas);         (* save current pragma state *)

  IF writeConfig. true THEN
    Out.String ("# version: ");
    WriteVersion;
    Out.String ("# initialization file: ");
    Out.String (topLevelConfig);
    Out.Ln;
    Parameter.WriteConfig
  ELSIF writeVersion. true THEN
    WriteVersion
  ELSE
    filterOptions := Filter.GetOptions();
    
    CASE mode. value OF
    | modeHelp:
      WriteHelp
    | modeHTML:
      moduleArgs := ModuleArguments (restArg);
      IF closure. true THEN
        Modules.Closure (moduleArgs, TRUE)
      END;
      WriteHTML (moduleArgs, filterOptions)
    | modeXRef:
      moduleArgs := ModuleArguments (restArg);
      IF closure. true THEN
        Modules.Closure (moduleArgs, TRUE)
      END;
      XRef.WriteXRef (moduleArgs, FALSE, lineNum. true, filterOptions)
    | modeModules:
      moduleArgs := ModuleArguments (restArg);
      IF closure. true THEN
        Modules.Closure (moduleArgs, noInternal. true)
      END;
      WriteModules (moduleArgs)
    | modeListUses:
      moduleArgs := ModuleArguments (restArg);
      IF closure. true THEN
        Modules.Closure (moduleArgs, TRUE)
      END;
      HTML.SetColors (colorSet. value^);
      XRef.WriteUses (moduleArgs, declName. value^)
    | modeInterface:
      moduleArgs := ModuleArguments (restArg);
      IF closure. true THEN
        Modules.Closure (moduleArgs, TRUE)
      END;
      IF (modeDef. value # mdefXRef) THEN
        WriteDefinition (moduleArgs, filterOptions)
      ELSE
        HTML.SetColors (colorSet. value^);
        XRef.WriteXRef (moduleArgs, TRUE, lineNum. true, filterOptions)
      END
    | modeFilter:
      moduleArgs := ModuleArguments (restArg);
      IF closure. true THEN
        Modules.Closure (moduleArgs, TRUE)
      END;
      WriteText (moduleArgs, filterOptions)
    END
  END
END oocn.
