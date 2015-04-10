(* 	$Id: oob.Mod,v 1.18 1999/08/08 18:31:19 acken Exp $	 *)
MODULE oob;
(*  Main module of symbol file browser.
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
  Out, ProgramArgs, TextRider, Filenames, Parameter, ParamOptions, ParamPaths,
  Config, StdPragmas, Error, Data, SymbolTable, SymbolFile, Browser;
  

VAR
  restArg, i: INTEGER;
  arg, dummy: Parameter.Filename;
  help, writeVersion: ParamOptions.BooleanOption;
  mod: Data.Object;
  noerr: BOOLEAN;
  
PROCEDURE WriteHelp;
  VAR
    argReader: TextRider.Reader;
    arg: Parameter.Filename;
  BEGIN
    Out.String ("Usage: ");
    argReader := TextRider.ConnectReader (ProgramArgs.args);
    argReader. ReadLine (arg);
    Out.String (arg);
    Out.String (" [options] <module-name>"); Out.Ln;
    Out.String ("Options: "); Out.Ln;
    Out.String ("--extended, -x            Include inherited fields and type-bound procedures"); Out.Ln;
    Out.String ("                          when writing a record."); Out.Ln;
    Out.String ("--config <file>           Use <file> as primary initialization file."); Out.Ln;
    Out.String ("--include-config <file>   Include initialization <file> in addition to the"); Out.Ln;
    Out.String ("                          default initialization file."); Out.Ln;
    Out.String ("--version                 Write compiler version and exit."); Out.Ln;
    Out.String ("--help, -h                Write this text and exit."); Out.Ln;
  END WriteHelp;

BEGIN
  ParamPaths.Init (TRUE, TRUE, TRUE);
  ParamOptions.Init (ParamOptions.acceptUndef);
  Parameter.include. CmdLineOption ("--include-config", "'$1'");
  
  help := ParamOptions.CreateBoolean ("help", FALSE);
  ParamOptions.options. Add (help);
  ParamOptions.options. CmdLineOption ("-h,--help", "help:=TRUE");
  
  writeVersion := ParamOptions.CreateBoolean ("writeVersion", FALSE);
  ParamOptions.options. Add (writeVersion);
  ParamOptions.options. CmdLineOption ("--version", "writeVersion:=TRUE");
  
  StdPragmas.Init;
  Parameter.ParseConfigFile (Config.defaultConfigFile,  Config.configEnvVar, 
                             "--config", TRUE, TRUE, dummy);
  restArg := Parameter.ParseCmdLine (TRUE, TRUE, TRUE);
  
  (* calling `ReadSymbolFile' may produce errors and warnings that are 
     signaled with the standard procedure `Error.ErrIns2'; thus we have to
     initialize the error module *)
  NEW (Error.sourceFile, 10);
  COPY ("*browser*", Error.sourceFile^);
  StdPragmas.warnings. Set (TRUE);
  Error.Init;
  SymbolTable.Init;
  
  IF writeVersion. true THEN
    Out.String (Config.defaultCompiler); Out.String ("/"); 
    Out.String (Config.defaultTargetArch); Out.String (" ");
    Out.String (Config.defaultCompilerVersion); Out.String (" for ");
    Out.String (Config.defaultTargetOS); Out.Ln
  ELSIF (restArg = 0) OR help. true THEN
    WriteHelp
  ELSE
    noerr := TRUE;
    FOR i := 0 TO restArg-1 DO
      Parameter.GetArg (0, arg);
      Filenames.GetFile (arg, arg);
      mod := SymbolFile.Read (arg, 0);
      noerr := noerr & Error.noerr & (mod # NIL);
      Error.EmitErrors (FALSE);
      IF (mod # NIL) THEN
        Browser.WriteModule (mod)
      END
    END;
    IF noerr THEN
      HALT (0)
    ELSE
      HALT (1)
    END
  END
END oob.
