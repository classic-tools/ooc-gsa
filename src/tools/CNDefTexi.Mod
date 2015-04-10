(*	$Id: CNDefTexi.Mod,v 1.3 1998/10/14 16:15:50 acken Exp $	*)
MODULE CNDefTexi;
(*  Generates a draft texinfo file from a module's public interface.
    Copyright (C) 1998  Michael van Acken

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
  StdChannels, TextRider, CharClass, Ascii, Strings,
  S := CNScanner, AST := CNAST, Decl := CNDecl;


TYPE
  Buffer = POINTER TO ARRAY OF CHAR;

VAR
  w: TextRider.Writer;
  buffer: Buffer;


PROCEDURE SetWriter* (writer: TextRider.Writer);
  BEGIN
    IF (writer = NIL) THEN
      w := TextRider.ConnectWriter (StdChannels.stdout)
    ELSE
      w := writer
    END
  END SetWriter;


PROCEDURE ClearInfo (sym: S.Symbol);
  BEGIN
    WHILE (sym # NIL) DO
      IF (sym. id = S.ident) & (sym. up IS AST.IdentDef) THEN
        sym. up(AST.IdentDef). info := NIL
      END;
      sym := sym. next
    END
  END ClearInfo;

PROCEDURE AttachComments (module: AST.Module);
(* Try to figure out to which declared name a comment belongs, and change 
   the corresponding `IdentDef's info field to refer to the comment.  *)
  VAR
    identDef: AST.IdentDef;
    sym: S.Symbol;
  
  PROCEDURE GetIdentDef (comment: S.Symbol): AST.IdentDef;
  (* Locate the definition for the given comment `comment'.  Result is NIL if
     no definition can be found.  *)
    VAR
      sym: S.Symbol;
      node: AST.Node;
      identDef: AST.IdentDef;
    BEGIN
      sym := comment. prev;
      LOOP
        IF (sym = NIL) OR (sym. id = S.comment) OR (sym IS S.StartSymbol) THEN
          RETURN NIL
        ELSIF (sym. id = S.pragma) OR (sym. id = S.comma) OR
              (sym. id = S.semicolon) THEN
          (* skip pragmas (they are discarded) and separators *)
          sym := sym. prev
        ELSE
          (* scan upward in syntax tree to the next body or declaration *)
          node := sym;
          WHILE ~(node IS AST.Decl) & ~(node IS AST.Body) DO
            node := node. up
          END;
          IF (node IS AST.Body) OR (node(AST.Decl). name = NIL) OR
             (node(AST.Decl). name. name. pos > comment. pos) THEN
            (* ignore statements, empty declarations, and names that are 
               declared after the comment *)
            RETURN NIL
          ELSE  (* locate last name in list before `comment' *)
            identDef := node(AST.Decl). name;
            WHILE (identDef. next # NIL) & 
                  (identDef. next. name. pos <= comment. pos) DO
              identDef := identDef. next
            END;
            RETURN identDef
          END
        END
      END
    END GetIdentDef;
  
  BEGIN
    sym := module. startSymbol. next;
    WHILE (sym # NIL) DO
      IF (sym. id = S.pragma) THEN
        sym. up := NIL
      ELSIF (sym. id = S.comment) THEN
        identDef := GetIdentDef (sym);
        IF (identDef # NIL) & (identDef. info = NIL) THEN
          identDef. info := sym
        END
      END;
      sym := sym. next
    END
  END AttachComments;

PROCEDURE WriteFlags (flags: AST.FlagList);
  VAR
    sym: S.Symbol;
  BEGIN
    IF (flags # NIL) THEN
      sym := flags. first;
      WHILE (sym # flags. last) DO
        IF (sym. id # S.comma) & (sym. id # S.pragma) THEN
          w. WriteString (sym. str^)
        END;
        sym := sym. next
      END
    END
  END WriteFlags;

PROCEDURE WriteName (ident: AST.Ident);
  BEGIN
    w. WriteString (ident. name. str^);
    IF (ident IS AST.IdentDef) THEN
      WriteFlags (ident(AST.IdentDef). flags)
    END
  END WriteName;

PROCEDURE WriteDescr (info: S.Info);
  VAR
    comment: S.TextSymbol;
  
  PROCEDURE ExtendBuffer (newLen: LONGINT);
    BEGIN
      IF (buffer = NIL) OR (newLen > LEN (buffer^)) THEN
        NEW (buffer, newLen+2048)
      END
    END ExtendBuffer;
  
  PROCEDURE StripComment (currLen: LONGINT);
    VAR
      i: LONGINT;
    BEGIN
      ASSERT (Strings.Length (buffer^) = currLen);
      
      buffer[0] := " ";
      i := 1;
      WHILE (buffer[i] = "*") OR CharClass.IsWhiteSpace (buffer[i]) DO
        buffer[i] := " ";
        INC (i)
      END;
      
      buffer[currLen-1] := " ";
      i := currLen-2;
      WHILE (i >= 0) & 
            ((buffer[i] = "*") OR CharClass.IsWhiteSpace (buffer[i])) DO
        buffer[i] := 0X;
        DEC (i)
      END
    END StripComment;
  
  PROCEDURE StripIndentation;
    VAR
      i, delta: LONGINT;
      bol: BOOLEAN;
    BEGIN
      bol := TRUE;
      delta := 0;
      i := 0;
      WHILE (buffer[i] # 0X) DO
        buffer[i-delta] := buffer[i];
        CASE buffer[i] OF
        | Ascii.cr, Ascii.lf:
          bol := TRUE
        | " ":
          IF bol THEN
            INC (delta)
          END
        ELSE
          bol := FALSE
        END;
        INC (i)
      END;
      buffer[i-delta] := 0X
    END StripIndentation;
  
  PROCEDURE QuoteChars;
    VAR
      i: INTEGER;
    BEGIN
      i := 0;
      WHILE (buffer[i] # 0X) DO
        CASE buffer[i] OF
        | "@", "{", "}":
          Strings.Insert ("@", i, buffer^);
          INC (i)
        ELSE (* leave as is *)
        END;
        INC (i)
      END
    END QuoteChars;
  
  BEGIN
    IF (info # NIL) THEN
      comment := info(S.TextSymbol);
      
      ExtendBuffer (LEN (comment. str^));
      COPY (comment. str^, buffer^);
      StripComment (LEN (comment. str^)-1);
      StripIndentation;
      QuoteChars;
      
      w. WriteString (buffer^);
      w. WriteLn
    END
  END WriteDescr;

PROCEDURE WriteDeclarations* (module: AST.Module);
  PROCEDURE Header (str: ARRAY OF CHAR);
    BEGIN
      w. WriteLn;
      w. WriteString ("@subheading ");
      w. WriteString (str);
      w. WriteLn;
    END Header;
  
  PROCEDURE WriteConstants (decl: AST.Decl);
    BEGIN
      Header ("Constants");
      
      WHILE (decl # NIL) DO
        IF (decl IS AST.ConstDecl) THEN
          w. WriteLn;
          w. WriteString ("@defvr {Constant} ");
          WriteName (decl. name);
          w. WriteLn;
          WriteDescr (decl. name. info);
          w. WriteString ("@end defvr");
          w. WriteLn
        END; 
        decl := decl. next
      END;
      w. WriteLn
    END WriteConstants;
  
  PROCEDURE ^ WriteTypeConstr (type: AST.Type; nested: BOOLEAN);
  
  PROCEDURE WriteFormalPars (fpars: AST.FormalPars);
    VAR
      section: AST.Decl;
      name: AST.IdentDef;
    BEGIN  (* pre: surrounding this piece of text is a @code{} *)
      WriteFlags (fpars. flags);
      
      w. WriteString ("(");
      section := fpars. fpSections;
      WHILE (section # NIL) DO
        IF (section # fpars. fpSections) THEN
          w. WriteString ("; ")
        END;
        IF (section(AST.FPSection). var # NIL) THEN
          w. WriteString ("VAR ")
        END;
        
        name := section. name;
        WHILE (name # NIL) DO
          IF (name # section. name) THEN
            w. WriteString (", ")
          END;
          w. WriteString ("@var{");
          WriteName (name);
          w. WriteString ("}");
          name := name. next
        END;
        
        IF (section(AST.FPSection). type # NIL) THEN
          w. WriteString (": ");
          WriteTypeConstr (section(AST.FPSection). type, TRUE)
        END;
        section := section. next
      END;
      w. WriteString (")");
      
      IF (fpars. resultType # NIL) THEN
        w. WriteString (": ");
        WriteTypeConstr (fpars. resultType, TRUE);
      END
    END WriteFormalPars;
  
  PROCEDURE WriteTypeConstr (type: AST.Type; nested: BOOLEAN);
    VAR
      i: LONGINT;
      expr: AST.Expr;
      decl: AST.IdentDef;
    
    PROCEDURE WriteFields (record: AST.Record);
      VAR
        fieldList: AST.Decl;
        name: AST.IdentDef;
      BEGIN
        fieldList := record. fields;
        WHILE (fieldList # NIL) DO
          name := fieldList(AST.FieldList). name;
          WHILE (name # NIL) DO
            w. WriteString ("@item Field: @b{");
            WriteName (name);
            w. WriteString ("}");
            IF (name. mark # NIL) & (name. mark. str^ = "-") THEN
              w. WriteString ("@minus{}")
            END;
            w. WriteString (": @code{");
            WriteTypeConstr (fieldList(AST.FieldList). type, TRUE);
            w. WriteString ("}");
            w. WriteLn;
            WriteDescr (name. info);
            w. WriteLn;
            name := name. next
          END;
          fieldList := fieldList. next
        END
      END WriteFields;
    
    BEGIN
      WITH type: AST.TypeName DO
        IF (type. qualident. module # NIL) THEN
          decl := Decl.GetDeclaration (type. qualident. module);
          WriteName (decl. up(AST.Import). module);
          w. WriteString (".")
        END;
        WriteName (type. qualident. ident)
        
      | type: AST.Array DO
        w. WriteString ("ARRAY");
        WriteFlags (type. flags);
        i := 0;
        expr := type. exprList;
        WHILE (expr # NIL) DO
          IF (expr # type. exprList) THEN
            w. WriteString (", ")
          ELSE
            w. WriteString (" ")
          END;
          w. WriteString ("n");
          w. WriteLInt (i, 0);
          INC (i);
          expr := expr. next
        END;
        w. WriteString (" OF ");
        WriteTypeConstr (type. type, FALSE)

      | type: AST.Record DO
        w. WriteString ("RECORD");
        WriteFlags (type. flags);
        IF (type. base # NIL) THEN
          w. WriteString (" (");
          WriteTypeConstr (type. base,  TRUE);
          w. WriteString (")")
        END;
        
        IF nested THEN
          w. WriteString (" [nested record fields discarded by oocn]")
        ELSE
          w. WriteLn;
          w. WriteString ("@table @asis");
          w. WriteLn;
          WriteFields (type);
          w. WriteString ("@end table")
        END

      | type: AST.Pointer DO
        w. WriteString ("POINTER");
        WriteFlags (type. flags);
        w. WriteString (" TO ");
        WriteTypeConstr (type. base, FALSE)

      | type: AST.ProcType DO
        w. WriteString ("PROCEDURE ");
        WriteFormalPars (type. fpars)
      END
    END WriteTypeConstr;
  
  PROCEDURE WriteTypes (decl: AST.Decl);
    CONST
      tpDataType = 0;
      tpRecord = 1;
      tpClass = 2;
      tpArray = 3;
    VAR
      tp: SHORTINT;
      
    PROCEDURE ClassOfType (type: AST.Type): SHORTINT;
      VAR
        ptrTp: SHORTINT;
        decl: AST.IdentDef;
      
      PROCEDURE HasTBProcs (type: AST.Type): BOOLEAN;
        VAR
          decl: AST.Decl;
          node: AST.Node;
        BEGIN
          node := type;
          WHILE ~(node IS AST.Module) DO
            node := node. up
          END;
          
          decl := node(AST.Module). body. declSeq;
          WHILE (decl # NIL) DO
            WITH decl: AST.ProcDecl DO
              IF (decl. receiver # NIL) & (Decl.BaseRecord (decl) = type) THEN
                RETURN TRUE
              END
            ELSE (* ignore *)
            END;
            decl := decl. next
          END;
          RETURN FALSE
        END HasTBProcs;
      
      BEGIN
        WITH type: AST.TypeName DO
          IF (type. qualident. module # NIL) THEN
            RETURN tpDataType
          ELSE
            decl := Decl.GetDeclaration (type. qualident. ident);
            IF (decl # NIL) & (decl. up. up IS AST.TypeDecl) THEN
              RETURN ClassOfType (decl. up. up(AST.TypeDecl). type)
            ELSE  (* imported type: ignore any details *)
              RETURN tpDataType
            END
          END
          
        | type: AST.Array DO
          RETURN tpArray
          
        | type: AST.Record DO
          IF (type. base # NIL) OR HasTBProcs (type) THEN
            RETURN tpClass
          ELSE
            RETURN tpRecord
          END
          
        | type: AST.Pointer DO
          ptrTp := ClassOfType (type. base);
          IF (ptrTp = tpClass) THEN
            RETURN tpClass
          ELSE
            RETURN tpDataType
          END
          
        | type: AST.ProcType DO
          RETURN tpDataType
        END
      END ClassOfType;
    
    BEGIN
      Header ("Types");
      
      WHILE (decl # NIL) DO
        IF (decl IS AST.TypeDecl) THEN
          w. WriteLn;
          w. WriteString ("@deftp ");
          tp := ClassOfType (decl(AST.TypeDecl). type);
          CASE tp OF
          | tpDataType: w. WriteString ("{Data type} ")
          | tpRecord  : w. WriteString ("Record ")
          | tpClass   : w. WriteString ("Class ")
          | tpArray   : w. WriteString ("Array ")
          END;
          WriteName (decl. name);
          w. WriteString (" = ");
          WriteTypeConstr (decl(AST.TypeDecl). type, FALSE);
          w. WriteLn;
          WriteDescr (decl. name. info);
          w. WriteString ("@end deftp");
          w. WriteLn
        END; 
        decl := decl. next
      END;
      w. WriteLn
    END WriteTypes;
  
  PROCEDURE WriteVariables (decl: AST.Decl);
    VAR
      name: AST.IdentDef;
    BEGIN
      Header ("Variables");
      
      WHILE (decl # NIL) DO
        IF (decl IS AST.VarDecl) THEN
          name := decl. name;
          WHILE (name # NIL) DO
            w. WriteLn;
            w. WriteString ("@defvr ");
            IF (name. mark # NIL) & (name. mark. str^ = "-") THEN
              w. WriteString ("{Read-only Variable} ")
            ELSE
              w. WriteString ("{Variable} ")
            END;
            WriteName (name);
            w. WriteString (": ");
            WriteTypeConstr (decl(AST.VarDecl). type, FALSE);
            w. WriteLn;
            WriteDescr (name. info);
            w. WriteString ("@end defvr");
            w. WriteLn;
            name := name. next
          END
        END; 
        decl := decl. next
      END;
      w. WriteLn
    END WriteVariables;
  
  PROCEDURE WriteProcedures (declList: AST.Decl);
    VAR
      proc, prev: AST.ProcDecl;
    
    PROCEDURE NextProc (prev: AST.ProcDecl): AST.ProcDecl;
      VAR
        prevBase, prevProc, bestBase, bestProc, declBase, declProc: LONGINT;
        best: AST.ProcDecl;
        decl: AST.Decl;
        
      PROCEDURE GetTuple (proc: AST.ProcDecl; VAR basePos, procPos: LONGINT);
        VAR
          record: AST.Record;
        BEGIN
          IF (proc = NIL) THEN
            basePos := 0; procPos := 0
          ELSE
            IF (proc. receiver # NIL) THEN
              record := Decl.BaseRecord (proc);
              basePos := record. record. pos
            ELSE
              basePos := 0
            END;
            procPos := proc. procedure. pos
          END
        END GetTuple;
      
      PROCEDURE Larger (b0, p0, b1, p1: LONGINT): BOOLEAN;
        (* (b0, p0) > (b1, p1) *)
        BEGIN
          RETURN (b0 > b1) OR (b0 = b1) & (p0 > p1)
        END Larger;
      
      BEGIN
        GetTuple (prev, prevBase, prevProc);
        best := NIL; bestBase := MAX (LONGINT); bestProc := MAX (LONGINT);
        
        decl := declList;
        WHILE (decl # NIL) DO
          WITH decl: AST.ProcDecl DO
            GetTuple (decl, declBase, declProc);
            IF Larger (declBase, declProc, prevBase, prevProc) &
               ~Larger (declBase, declProc, bestBase, bestProc) THEN
              best := decl; bestBase := declBase; bestProc := declProc
            END
          ELSE
          END;
          decl := decl. next
        END;
        
        RETURN best
      END NextProc;
    
    BEGIN
      Header ("Procedures");
      
      prev := NIL;
      proc := NextProc (NIL);
      WHILE (proc # NIL) DO
        w. WriteLn;
        
        IF (proc. receiver # NIL) THEN
          IF (prev = NIL) OR (prev. receiver = NIL) THEN
            w. WriteString ("@table @asis");
            w. WriteLn
          ELSIF (Decl.BaseRecord (prev) # Decl.BaseRecord (proc)) THEN
            (* note: we never switch back from type-bound to normal procs *)
            w. WriteString ("@end table");
            w. WriteLn;
            w. WriteLn;
            w. WriteString ("@table @asis");
            w. WriteLn
          END;
          
          w. WriteString ("@item Method: @code{");
          WriteFormalPars (proc. receiver);
          w. WriteString ("} @b{");
          WriteName (proc. name);
          w. WriteString ("}")
        ELSE
          w. WriteString ("@deffn ");
          IF (proc. fpars. resultType = NIL) THEN
            w. WriteString ("Procedure ")
          ELSE
            w. WriteString ("Function ")
          END;
          WriteName (proc. name)
        END;

        w. WriteString (" @code{");
        WriteFormalPars (proc. fpars);
        w. WriteString ("}");

        w. WriteLn;
        WriteDescr (proc. name. info);
        IF (proc. receiver = NIL) THEN
          w. WriteString ("@end deffn");
          w. WriteLn
        END;
        
        prev := proc;
        proc := NextProc (proc)
      END;
      
      IF (prev # NIL) & (prev. receiver # NIL) THEN
        w. WriteLn;
        w. WriteString ("@end table");
        w. WriteLn
      END;
      
      w. WriteLn
    END WriteProcedures;
  
  BEGIN
    ClearInfo (module. startSymbol. next);
    AttachComments (module);
    
    WriteConstants (module. body. declSeq);
    WriteTypes (module. body. declSeq);
    WriteVariables (module. body. declSeq);
    WriteProcedures (module. body. declSeq);
    ClearInfo (module. startSymbol. next)
  END WriteDeclarations;

BEGIN
  SetWriter (NIL);
  buffer := NIL
END CNDefTexi.
