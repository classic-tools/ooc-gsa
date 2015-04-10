MODULE oowhereis;
(*  File finder.
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
  Out, ProgramArgs, TextRider, Parameter, ParamOptions, ParamPaths, RCS, 
  Strings, Config, Filenames;


CONST
  moduleSeparator = ":";
  dirSeparator = "/";
  
VAR
  rcsMaster, help, writeVersion: ParamOptions.BooleanOption;
  restArg: INTEGER;  
  dummy: Parameter.Filename;

PROCEDURE WriteHelp;
  VAR
    argReader: TextRider.Reader;
    arg: Parameter.Filename;
  BEGIN
    Out.String ("Usage: ");
    argReader := TextRider.ConnectReader (ProgramArgs.args);
    argReader. ReadLine (arg);
    Out.String (arg);
    Out.String (" [options] <file>"); Out.Ln;
    Out.String ("Options:"); Out.Ln;
    Out.String ("--rcs-master,-r           Don't convert name of RCS master to working file.");  Out.Ln;
    Out.String ("--config <file>           Use <file> as primary initialization file."); Out.Ln;
    Out.String ("--include-config <file>   Include initialization <file> in addition to the"); Out.Ln;
    Out.String ("                          default initialization file."); Out.Ln;
    Out.String ("--version                 Write compiler version and exit."); Out.Ln;
    Out.String ("--help, -h                Write this text and exit."); Out.Ln;
  END WriteHelp;


PROCEDURE Query(): BOOLEAN;
  VAR
    arg, file, ext: Parameter.Filename;
    keepGivenPath, found: BOOLEAN;
    pos: INTEGER;
  BEGIN
    Parameter.GetArg (0, arg);   (* get first argument after the option list *)
    keepGivenPath := TRUE;
    
    (* if there is no directory part in the given name, and the file name
       extension is ".Mod", then replace all occurences of `moduleSeparator'
       with `dirSeparator'  *)
    Strings.FindNext (dirSeparator, arg, 0, found, pos);
    Filenames.GetExt (arg, file, ext);
    IF ~found & (ext = Config.moduleExtension) THEN
      keepGivenPath := FALSE;
      pos := 0;
      WHILE (arg[pos] # 0X) DO
        IF (arg[pos] = moduleSeparator) THEN
          arg[pos] := dirSeparator
        END;
        INC (pos)
      END
    END;
    
    IF ParamPaths.FindPath (arg, keepGivenPath, file) THEN
      IF ~rcsMaster. true & RCS.MasterFile (file) THEN
        RCS.Master2File (file, file)
      END;
      Out.String (file);
      Out.Ln;
      RETURN TRUE
    ELSE
      Out.String ("Can't find file ");
      Out.String (arg);
      Out.Ln;
      RETURN FALSE
    END;
  END Query;

BEGIN
  ParamPaths.Init (TRUE, TRUE, TRUE);
  ParamOptions.Init (ParamOptions.ignoreUndef);
  Parameter.include. CmdLineOption ("--include-config", "'$1'");
  
  rcsMaster := ParamOptions.CreateBoolean ("rcsMaster", FALSE);
  ParamOptions.options. Add (rcsMaster);
  ParamOptions.options. CmdLineOption ("--rcs-master,-r", "rcsMaster:=TRUE");
  
  help := ParamOptions.CreateBoolean ("help", FALSE);
  ParamOptions.options. Add (help);
  ParamOptions.options. CmdLineOption ("-h,--help", "help:=TRUE");
  
  writeVersion := ParamOptions.CreateBoolean ("writeVersion", FALSE);
  ParamOptions.options. Add (writeVersion);
  ParamOptions.options. CmdLineOption ("--version", "writeVersion:=TRUE");
  
  Parameter.ParseConfigFile (Config.defaultConfigFile,  Config.configEnvVar, 
                             "--config", TRUE, TRUE, dummy);
  restArg := Parameter.ParseCmdLine (TRUE, TRUE, TRUE);
  
  IF writeVersion. true THEN
    Out.String (Config.defaultCompiler); Out.String ("/"); 
    Out.String (Config.defaultTargetArch); Out.String (" ");
    Out.String (Config.defaultCompilerVersion); Out.String (" for ");
    Out.String (Config.defaultTargetOS); Out.Ln
  ELSIF (restArg # 1) OR help. true THEN
    WriteHelp
  ELSE
    IF Query() THEN
      HALT (0)
    ELSE
      HALT (1)
    END
  END
END oowhereis.
