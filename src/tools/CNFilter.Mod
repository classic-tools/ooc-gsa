(*	$Id: CNFilter.Mod,v 1.5 1999/08/08 08:22:57 acken Exp $	*)
MODULE CNFilter;
(*  Simple code transformation on AST.
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
  Strings, ParamOptions, S := CNScanner, AST := CNAST;

TYPE
  Set* = SET;
  
CONST
  removeComments* = 0;
  removeDocStrings* = 1;
  removePragmas* = 2;
  removeSystemFlags* = 3;
  addForeign* = 4;
  removeForeign* = 5;
  removeMIdent* = 6;
  noOperation* = {};
  
VAR
  stripComments: ParamOptions.BooleanOption;
  stripDocStrings: ParamOptions.BooleanOption;
  stripPragmas: ParamOptions.BooleanOption;
  stripSystemFlags: ParamOptions.BooleanOption;
  handleForeign: ParamOptions.IntegerOption;
  stripMIdent: ParamOptions.BooleanOption;


PROCEDURE GetOptions*(): Set;
  VAR
    set: Set;
  BEGIN
    set := {};
    IF stripComments. true THEN INCL (set, removeComments) END;
    IF stripDocStrings. true THEN INCL (set, removeDocStrings) END;
    IF stripPragmas. true THEN INCL (set, removePragmas) END;
    IF stripSystemFlags. true THEN INCL (set, removeSystemFlags) END;
    IF handleForeign. value = 0 THEN INCL (set, removeForeign) END;
    IF handleForeign. value = 1 THEN INCL (set, addForeign) END;
    IF stripMIdent. true THEN INCL (set, removeMIdent) END;
    RETURN set
  END GetOptions;

PROCEDURE Foreign (module: AST.Module; on: BOOLEAN);
  VAR
    sym: AST.Symbol;
    ident: AST.IdentDef;
    decl: AST.Decl;
    str: ARRAY 1024 OF CHAR;
    statm, nextStatm: AST.Statement;
  BEGIN
    ident := module. name;
    IF (ident. flags # NIL) THEN
      ident. flags. Remove;
      ident. flags := NIL
    END;
    
    IF on THEN  (* add FOREIGN module flags, remove procedure bodies *)
      COPY (module. name. name. str^, str);
      Strings.Insert ('[FOREIGN "C"; LINK FILE "', 0, str);
      Strings.Append ('.c" END]', str);
      module. name. name. Insert (S.NewSymbol (str, 0, 1, S.undefPos));
      
      decl := module. body. declSeq;
      WHILE (decl # NIL) DO
        IF (decl IS AST.ProcDecl) & (decl(AST.ProcDecl). body # NIL) THEN
          decl(AST.ProcDecl). body. Remove;
          decl(AST.ProcDecl). body := NIL;
          decl(AST.ProcDecl). semicolon2. Remove;
          decl(AST.ProcDecl). semicolon2 := NIL
        END;
        decl := decl. next
      END;
      
      IF (module. body # NIL) THEN
        IF (module. body. begin # NIL) THEN
          module. body. begin. Remove;
          module. body. begin := NIL
        END;
        statm := module. body. statmSeq;
        WHILE (statm # NIL) DO
          nextStatm := statm. next;
          statm. Remove;
          statm := nextStatm
        END;
        module. body. statmSeq := NIL
      END
      
    ELSE  (* replace module flags by OOC_EXTENSIONS, add procedure bodies *)
      ident. name. Insert (S.NewSymbol ("[OOC_EXTENSIONS]", 0, 1, S.undefPos));
      
      decl := module. body. declSeq;
      WHILE (decl # NIL) DO
        IF (decl IS AST.ProcDecl) & (decl(AST.ProcDecl). body = NIL) THEN
          COPY (decl. name. name. str^, str);
          Strings.Insert ("END ", 0, str);
          Strings.Append (";", str);
          sym := decl(AST.ProcDecl). semicolon1;
          WHILE (sym. next. id = S.comment) & (sym. next. line < 2) DO
            sym := sym. next
          END;
          sym. Insert (S.NewSymbol (str, 1, 2, S.undefPos))
        END;
        decl := decl. next
      END
    END
  END Foreign;

PROCEDURE RemoveMIdent (module: AST.Module);
  VAR
    shrunk, last: ARRAY 1024 OF CHAR;
    decl: AST.Decl;
    import: AST.Import;
    sym, oldModule: AST.Symbol;
  
  PROCEDURE IsMIdent (VAR name, shrunk, last: ARRAY OF CHAR): BOOLEAN;
    CONST
      sep = ":";
    VAR
      i, j, lastStart: LONGINT;
    BEGIN
      lastStart := 0;
      i := 0;
      j := 0;
      WHILE (name[i] # 0X) DO
        IF (name[i] # sep) THEN
          IF (j < LEN(shrunk)-1) THEN
            shrunk[j] := name[i];
            INC (j)
          END
        ELSE
          lastStart := i+1
        END;
        INC (i)
      END;
      shrunk[j] := 0X;
      
      i := lastStart;
      j := 0;
      WHILE (name[i] # 0X) DO
        IF (j < LEN (last)-1) THEN
          last[j] := name[i];
          INC (j)
        END;
        INC (i)
      END;
      last[j] := 0X;
      
      RETURN (lastStart # 0)
    END IsMIdent;
  
  PROCEDURE Replace (VAR old: AST.Symbol; VAR with: ARRAY OF CHAR);
    VAR
      new: AST.Symbol;
    BEGIN
      new := S.NewSymbol (with, old. line, old. column, old. pos);
      old. Insert (new);
      old. Remove;
      old := new
    END Replace;
  
  BEGIN
    IF IsMIdent (module. name. name. str^, shrunk, last) THEN
      Replace (module. name. name, shrunk);
      Replace (module. body. name. name, shrunk)
    END;
      
    IF (module. importList # NIL) THEN
      decl := module. importList. imports;
      WHILE (decl # NIL) DO
        import := decl(AST.Import);
        IF IsMIdent (import. module. name. str^, shrunk, last) THEN
          IF (import. becomes = NIL) THEN
            oldModule := import. module. name;

            import. name. up := import;
            oldModule. prev. Insert (import. name. name);

            sym := S.NewSymbol (":=", 0, 1, oldModule. pos);
            sym. up := import;
            import. becomes := sym;
            oldModule. prev. Insert (sym);

            import. module. name. CopyCoord (import. name. name, TRUE);
            import. becomes. CopyCoord (import. module. name, TRUE)
          END;
          
          Replace (import. module. name, shrunk)
        END;
        decl := decl. next
      END
    END
  END RemoveMIdent;

PROCEDURE Apply* (start: S.StartSymbol; remove: Set);
  VAR
    sym, next: S.Symbol;
    node: AST.Node;
  
  PROCEDURE ClearFlagList (node: AST.Node);
    BEGIN
      WITH node: AST.IdentDef DO node. flags := NIL
      | node: AST.Array       DO node. flags := NIL
      | node: AST.Record      DO node. flags := NIL
      | node: AST.Pointer     DO node. flags := NIL
      | node: AST.FormalPars  DO node. flags := NIL
      | node: AST.ProcDecl    DO node. flags := NIL
      END
    END ClearFlagList;
  
  BEGIN
    sym := start. next;
    WHILE (sym # NIL) DO
      next := sym. next;
      CASE sym. id OF
      | S.comment:
        IF (removeComments IN remove) & ~S.DocString (sym) OR
           (removeDocStrings IN remove) & S.DocString (sym) THEN
          sym. Remove  (* no node has pointers to comments *)
        END
      | S.pragma:
        IF (removePragmas IN remove) THEN
          sym. Remove  (* no node has pointers to pragmas *)
        END
      | S.lBrak:
        IF (removeSystemFlags IN remove) & (sym. up IS AST.FlagList) THEN
          next := sym. up(AST.FlagList). last. NextSym();
          ClearFlagList (sym. up. up);
          sym. up. Remove
        END
      ELSE  (* ignore all other symbols *)
      END;
      sym := next
    END;
    
    node := start;
    WHILE (node. up = NIL) DO node := node(AST.Symbol). next END;
    WHILE (node. up # NIL) DO node := node. up END;
    IF (addForeign IN remove) OR (removeForeign IN remove) THEN
      Foreign (node(AST.Module), addForeign IN remove)
    END;
    IF (removeMIdent IN remove) THEN
      RemoveMIdent (node(AST.Module))
    END
  END Apply;

BEGIN
  stripComments := ParamOptions.CreateBoolean ("stripComments", FALSE);
  ParamOptions.options. Add (stripComments);
  ParamOptions.options. CmdLineOption ("--strip-comments", "stripComments:=TRUE");
  
  stripDocStrings := ParamOptions.CreateBoolean ("stripDocStrings", FALSE);
  ParamOptions.options. Add (stripDocStrings);
  ParamOptions.options. CmdLineOption ("--strip-doc-strings", "stripDocStrings:=TRUE");
  
  stripPragmas := ParamOptions.CreateBoolean ("stripPragmas", FALSE);
  ParamOptions.options. Add (stripPragmas);
  ParamOptions.options. CmdLineOption ("--strip-pragmas", "stripPragmas:=TRUE");
  
  stripSystemFlags := ParamOptions.CreateBoolean ("stripSystemFlags", FALSE);
  ParamOptions.options. Add (stripSystemFlags);
  ParamOptions.options. CmdLineOption ("--strip-system-flags", "stripSystemFlags:=TRUE");

  handleForeign := ParamOptions.CreateInteger ("handleForeign", -1, -1, 1);
  ParamOptions.options. Add (handleForeign);
  ParamOptions.options. CmdLineOption ("--mod2foreign", "handleForeign:=1");
  ParamOptions.options. CmdLineOption ("--foreign2mod", "handleForeign:=0");

  stripMIdent := ParamOptions.CreateBoolean ("stripMIdent", FALSE);
  ParamOptions.options. Add (stripMIdent);
  ParamOptions.options. CmdLineOption ("--strip-mident", "stripMIdent:=TRUE");
END CNFilter.
