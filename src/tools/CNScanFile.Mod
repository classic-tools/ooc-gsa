(* 	$Id: CNScanFile.Mod,v 1.2 1999/11/14 19:19:52 ooc-devel Exp $	 *)
MODULE CNScanFile;
(*  File scanner with Texinfo add-on.
    Copyright (C) 1999  Michael van Acken

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
  ParamOptions, S := CNScanner, Texinfo := CNTexinfo;
  
VAR  
  parseTexinfo: ParamOptions.BooleanOption;
  (* if `parseTexinfo. true=TRUE', then parse and reformat any comments that
     have Texinfo commands embedded into them *)


PROCEDURE Scan* (fileName: ARRAY OF CHAR): S.StartSymbol;
(* Scans file by calling `Scanner.ScanFile', and subsequently parses all
   comments as Texinfo text, if the file's comments contain any Texinfo
   commands.  *)
  VAR
    start: S.StartSymbol;
    sym: S.Symbol;
    err: BOOLEAN;
  BEGIN
    start := S.ScanFile (fileName);
    err := FALSE;

    IF parseTexinfo. true THEN
      (* add parsed Texinfo data to comment symbols *)
      sym := start. next;
      WHILE (sym # NIL) DO
        IF (sym. id = S.comment) &
           Texinfo.IsTexinfo (sym(S.TextSymbol). str^) THEN
          sym(S.TextSymbol). info := Texinfo.Parse (sym(S.TextSymbol));
          err := err OR (sym(S.TextSymbol). info = NIL)
        END;
        sym := sym. next
      END;
      IF err THEN  (* the tokenizer or the parser ran into an error *)
        HALT (1)
      END
    END;
    
    RETURN start
  END Scan;

BEGIN
  parseTexinfo := ParamOptions.CreateBoolean ("parseTexinfo", TRUE);
  ParamOptions.options. Add (parseTexinfo);
  ParamOptions.options. CmdLineOption ("--no-texinfo", "parseTexinfo:=FALSE")
END CNScanFile.
