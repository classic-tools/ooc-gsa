(*	$Id: CNOutput.Mod,v 1.5 2000/04/22 15:03:00 ooc-devel Exp $	*)
MODULE CNOutput;
(*  Handles output redirection for the client modules.
    Copyright (C) 1998-2000  Michael van Acken

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
  Channel, Files, StdChannels, Strings, Filenames, Out, 
  Parameter, ParamOptions;


VAR
  outputDir: ParamOptions.StringOption;
  (* either a directory name, or "-" to denote stdout *)
  verbose: ParamOptions.BooleanOption;
  (* if `verbose. true=TRUE', write strings passed to `VerboseMsg' to stdout, 
     otherwise ignore them *)



PROCEDURE ToStdout* (): BOOLEAN;
  BEGIN
    RETURN (outputDir. value^ = "-")
  END ToStdout;

PROCEDURE VerboseMsg* (part0, part1: ARRAY OF CHAR);
(* Writes `part0part1' plus newline to stdout, unless `verbose. true' is 
   FALSE. *)
  BEGIN
    IF verbose. true & ~ToStdout() THEN
      Out.String (part0);
      Out.String (part1);
      Out.Ln;
      Out.Flush
    END
  END VerboseMsg;

PROCEDURE FatalError* (msg: ARRAY OF CHAR);
  BEGIN
    Parameter.FatalError (msg)
  END FatalError;

PROCEDURE FixModuleName* (VAR modName: ARRAY OF CHAR);
  VAR
    i: LONGINT;
  BEGIN
    i := 0;
    WHILE (modName[i] # 0X) DO         (* replace ":" with "_" *)
      IF (modName[i] = ":") THEN
        modName[i] := "_"
      END;
      INC (i)
    END
  END FixModuleName;


PROCEDURE Open* (modName, suffix1, suffix2: ARRAY OF CHAR): Channel.Channel;
  VAR
    file: Files.File;
    filename: Parameter.Filename;
    res: Files.Result;
  BEGIN
    IF ToStdout() THEN
      RETURN StdChannels.stdout
    ELSE
      COPY (modName, filename);
      FixModuleName (filename);
      Strings.Append (suffix1, filename);
      Filenames.BuildFilename (filename, outputDir. value^, filename, suffix2);
      file := Files.New (filename, {Files.write}, res);
      IF (file = NIL) THEN
        Out.String ("Error creating file ");
        Out.String (filename);
        Out.String (":");
        Out.Ln;
        res. GetText (filename);
        Out.String (filename);
        Out.Ln;
        HALT (1)
      ELSE
        VerboseMsg ("+ ", filename)
      END;
      RETURN file
    END
  END Open;

PROCEDURE Close* (ch: Channel.Channel);
  BEGIN
    IF ~ToStdout() THEN
      ch. Close
    END
  END Close;


BEGIN
  outputDir := ParamOptions.CreateString ("outputDir", "");
  ParamOptions.options. Add (outputDir);
  ParamOptions.options. CmdLineOption ("-o", "outputDir:='$1'");

  verbose := ParamOptions.CreateBoolean ("verbose", FALSE);
  ParamOptions.options. Add (verbose);
  ParamOptions.options. CmdLineOption ("-v,--verbose", "verbose:=TRUE")
END CNOutput.
