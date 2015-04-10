(*	$Id: CNModuleDef.Mod,v 1.4 1999/11/22 21:17:57 ooc-devel Exp $	*)
MODULE CNModuleDef;
(*  Extracts the public interface of a module from its syntax tree.
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
  CharClass,
  S := CNScanner, AST := CNAST;


VAR
  lastRemoved: S.Symbol;  (* symbol behind last removed stretch of code *)
  

PROCEDURE Remove (node: AST.Node);
(* pre: calls to `Remove' are made in ascending order with regard to the
        source code position of `node' *)
  VAR
    first, last, sym, next: S.Symbol;
  
  PROCEDURE CopyCoord (from, to: S.Symbol);
  (* This is a hack to improve the output quality.  Basically it keeps some
     newline characters in the output.  Import statements profit from this,
     and some additional empty lines are kept from the input file.  *)
    BEGIN
      IF (to # NIL) & (from. line > to. line) &
         CharClass.IsLetter (to. str[0]) THEN
        from. CopyCoord (to, to. str^ # "END")
      END
    END CopyCoord;
  
  BEGIN
    first := node. FirstSym();
    last := node. LastSym();
    
    IF (lastRemoved # NIL) THEN
      (*IF (ABS (first. pos) < ABS (lastRemoved. pos)) THEN
        Log.LongInt ("lastRemoved", ABS(lastRemoved.pos));
        Log.LongInt ("first", ABS(first.pos));
      END;*)
      ASSERT (ABS (first. pos) >= ABS (lastRemoved. pos))
    END;
    
    IF (lastRemoved # NIL) & (lastRemoved. id = S.comment) THEN
      (* if there are only comments between the last removed piece of source
         code and the piece of code denoted by `node', then remove the comments
         in between as well *)
      sym := lastRemoved;
      WHILE (sym # first) & (sym. id = S.comment) DO
        sym := sym. next
      END;
      
      IF (sym = first) THEN
        CopyCoord (lastRemoved, first);
        sym := lastRemoved;
        WHILE (sym # first) DO
          next := sym. next;
          sym. Remove;
          sym := next
        END
      END
    END;
    
    CopyCoord (first, last. next);
    lastRemoved := last. next;  (* first symbol after the removed interval *)
    node. Remove
  END Remove;



PROCEDURE RemoveComments (ast: AST.Module; VAR foundDocString: BOOLEAN);
(* Discards all pragmas, and, if a single doc comment is found in the module,
   all normal comments.  *)
  VAR
    sym, next: S.Symbol;
  BEGIN
    foundDocString := FALSE;
    
    sym := ast. startSymbol. next;
    WHILE (sym # NIL) DO
      IF (sym. id = S.pragma) THEN
        sym. Remove
      ELSIF (sym. id = S.comment) & S.DocString (sym) THEN
        foundDocString := TRUE
      END;
      sym := sym. next
    END;
    
    IF foundDocString THEN
      sym := ast. startSymbol. next;
      WHILE (sym # NIL) DO
        next := sym. next;
        IF (sym. id = S.comment) & ~S.DocString (sym) THEN
          sym. Remove
        END;
        sym := next
      END
    END
  END RemoveComments;

PROCEDURE RemoveLocalNames (VAR identList: AST.IdentDef);
  VAR
    name, next: AST.IdentDef;
  BEGIN  (* pre: at least one identifier of the list is exported *)
    name := identList;
    WHILE (name # NIL) DO
      next := name. next;

      IF (name. mark = NIL) THEN  (* remove private field/variable *)
        IF (name. prev = NIL) THEN
          identList := name. next
        ELSE
          name. prev. next := name. next
        END;
        IF (name. next # NIL) THEN
          name. next. prev := name. prev
        END;
        
        IF (name. prev # NIL) THEN
          (* ugly hack to keep ascending order when calling `Remove' *)
          Remove (name. prev. comma);
          name. prev. comma := name. comma;
          IF (name. comma # NIL) THEN
            name. comma. up := name. prev;
            name. comma := NIL
          END
        END;
        Remove (name)
      END;

      name := next
    END
  END RemoveLocalNames;

PROCEDURE ^ MarkDecl (ast: AST.Module; name: AST.IdentDef);

PROCEDURE ScanDecl (ast: AST.Module; decl: AST.Decl; remove: BOOLEAN);
(*  remove=FALSE: mark all declarations used by `decl'
    remove=TRUE: remove any field declarations local to `decl' that are not
      exported  *)

  PROCEDURE ^ ScanType (type: AST.Type);

  PROCEDURE ScanFormalPars (fpars: AST.FormalPars);
    VAR
      fpSection: AST.Decl;
    BEGIN
      IF (fpars # NIL) THEN
        fpSection := fpars. fpSections;
        WHILE (fpSection # NIL) DO
          ScanType (fpSection(AST.FPSection). type);
          fpSection := fpSection. next
        END;
        ScanType (fpars. resultType)
      END
    END ScanFormalPars;

  PROCEDURE ScanQualident (qident: AST.Qualident);
    VAR
      decl: AST.Decl;
      name: AST.IdentDef;
    BEGIN
      IF ~remove THEN
        IF (qident. module # NIL) THEN
          (* qualified identifier: mark module import *)
          decl := ast. importList. imports;
          WHILE (decl. name. name. str^ # qident. module. name. str^) DO
            decl := decl. next
          END;
          IF (decl. name. name. pos > 0) THEN
            decl. name. name. NegatePos()
          END
        ELSE
          (* locally declared identifier: get declaration and mark it; note 
             that the name can refer to a predefined entity *)
          name := NIL;
          decl := ast. body. declSeq;
          WHILE (decl # NIL) & (name = NIL) DO
            name := decl. name;
            WHILE (name # NIL) &
                  (name. name. str^ # qident. ident. name. str^) DO
              name := name. next
            END;
            decl := decl. next
          END;
          IF (name # NIL) & ~remove THEN
            MarkDecl (ast, name)
          END
        END
      END
    END ScanQualident;

  PROCEDURE ScanExpr (expr: AST.Expr);
    VAR
      e: AST.Expr;
      se: AST.SetElement;
    BEGIN
      IF (expr # NIL) THEN
        WITH expr: AST.Operator DO
          ScanExpr (expr. left);
          ScanExpr (expr. right)
        | expr: AST.FctCall DO
          ScanQualident (expr. design. qualident);
          e := expr. arguments;
          WHILE (e # NIL) DO
            ScanExpr (e);
            e := e. next
          END
        | expr: AST.FactorExpr DO
          ScanExpr (expr. expr)
        | expr: AST.Set DO
          se := expr. elements;
          WHILE (se # NIL) DO
            ScanExpr (se. lower);
            ScanExpr (se. upper);
            se := se. next
          END
        | expr: AST.Literal DO
        END
      END
    END ScanExpr;

  PROCEDURE ScanType (type: AST.Type);
    VAR
      flist, next: AST.Decl;
      expr: AST.Expr;

    PROCEDURE FieldList (VAR head: AST.Decl; flist: AST.FieldList);
    (* Scan declaration of field list for used type names.  Remove any
       names that are not marked as exported.  *)

      PROCEDURE RemoveAll (flist: AST.FieldList): BOOLEAN;
        VAR
          name: AST.IdentDef;
        BEGIN
          IF (flist. name = NIL) THEN  (* keep empty field list *)
            RETURN FALSE
          ELSE
            name := flist. name;
            WHILE (name # NIL) DO
              IF (name. mark # NIL) THEN
                RETURN FALSE
              END;
              name := name. next
            END;
            RETURN TRUE
          END
        END RemoveAll;

      BEGIN
        IF remove THEN
          IF RemoveAll (flist) THEN  (* remove whole field list *)
            IF (flist = head)  THEN
              head := flist. next
            ELSE
              flist. prev. next := flist. next
            END;
            IF (flist. next # NIL) THEN
              flist. next. prev := flist. prev
            END;
            Remove (flist)
          ELSE  (* only remove not exported names *)
            RemoveLocalNames (flist. name)
          END

        ELSIF ~RemoveAll (flist) THEN
          ScanType (flist. type)
        END
      END FieldList;

    BEGIN
      IF (type # NIL) THEN
        WITH type: AST.TypeName DO
          ScanQualident (type. qualident)

        | type: AST.Array DO
          expr := type. exprList;
          WHILE (expr # NIL) DO
            ScanExpr (expr);
            expr := expr. next
          END;
          ScanType (type. type)

        | type: AST.Record DO
          ScanType (type. base);
          flist := type. fields;
          WHILE (flist # NIL) DO
            next := flist. next;
            FieldList (type. fields, flist(AST.FieldList));
            flist := next
          END

        | type: AST.Pointer DO
          ScanType (type. base)

        | type: AST.FormalPars DO
          ScanFormalPars (type)

        | type: AST.ProcType DO
          ScanFormalPars (type. fpars)
        END
      END
    END ScanType;

  BEGIN
    WITH decl: AST.ConstDecl DO
      ScanExpr (decl. value)

    | decl: AST.TypeDecl DO
      ScanType (decl. type)

    | decl: AST.VarDecl DO
      ScanType (decl. type)

    | decl: AST.ProcDecl DO
      ScanFormalPars (decl. receiver);
      ScanFormalPars (decl. fpars)
    (* AST.FieldList, AST.FPSection, AST.Import are not valid here *)
    END
  END ScanDecl;

PROCEDURE MarkDecl (ast: AST.Module; name: AST.IdentDef);
  BEGIN  (* pre: ~remove *)
    IF (name. name. pos > 0) THEN
      name. name. NegatePos();
      ScanDecl (ast, name. up(AST.Decl), FALSE)
    END
  END MarkDecl;

PROCEDURE MarkInterface (ast: AST.Module);
(* This procedure marks all top-level declarations that are exported, or that
   are used indirectly by an exported declaration.  Such declarations are 
   marked with a negative `pos' field.  *)
  VAR
    decl: AST.Decl;
    name: AST.IdentDef;
  BEGIN  (* pre: ~remove *)
    decl := ast. body. declSeq;
    WHILE (decl # NIL) DO
      name := decl. name;
      
      (* mark all exported names *)
      WHILE (name # NIL) DO
        IF (name. mark # NIL) THEN
          MarkDecl (ast, name)
        END;
        name := name. next
      END;
      
      decl := decl. next
    END
  END MarkInterface;

PROCEDURE RemoveLocalDecl (ast: AST.Module);
  VAR
    decl, next: AST.Decl;
    statm, nextStatm: AST.Statement;
  
  PROCEDURE RemoveDecl (decl: AST.Decl);
    BEGIN
      IF (decl. prev = NIL) THEN
        ast. body. declSeq := decl. next
      ELSE
        decl. prev. next := decl. next
      END;
      IF (decl. next # NIL) THEN
        decl. next. prev := decl. prev
      END;
      
      Remove (decl)
    END RemoveDecl;
  
  PROCEDURE RemoveProcBody (proc: AST.ProcDecl);
  (* Removes the body of the procedure, including any declarations local to 
     the procedure.  *)
    BEGIN
      IF (proc. body # NIL) THEN
        Remove (proc. body);
        proc. body := NIL;
        Remove (proc. semicolon2);
        proc. semicolon2 := NIL
      END
    END RemoveProcBody;
    
  PROCEDURE Exported (name: AST.IdentDef): BOOLEAN;
    BEGIN
      WHILE (name # NIL) & (name. name. pos > 0) DO
        name := name. next
      END;
      RETURN (name # NIL)
    END Exported;
  
  PROCEDURE ImportEmpty (ilist: AST.Decl): BOOLEAN;
    BEGIN
      WHILE (ilist # NIL) DO
        IF (ilist. name. name. pos < 0) THEN
          RETURN FALSE
        END;
        ilist := ilist. next
      END;
      RETURN TRUE
    END ImportEmpty;
  
  PROCEDURE RemoveAllConst (decl: AST.Decl): BOOLEAN;
  (* TRUE iff the whole `ConstDecl' starting with `decl' will be removed.  *)
    BEGIN
      REPEAT
        IF (decl. name. name. pos < 0) THEN
          RETURN FALSE
        END;
        decl := decl. next
      UNTIL ~(decl IS AST.ConstDecl) OR
            (decl(AST.ConstDecl). constKW # NIL);
      RETURN TRUE
    END RemoveAllConst;
  
  PROCEDURE RemoveAllType (decl: AST.Decl): BOOLEAN;
  (* TRUE iff the whole `TypeDecl' starting with `decl' will be removed.  *)
    BEGIN
      REPEAT
        IF (decl. name. name. pos < 0) THEN
          RETURN FALSE
        END;
        decl := decl. next
      UNTIL ~(decl IS AST.TypeDecl) OR
            (decl(AST.TypeDecl). typeKW # NIL);
      RETURN TRUE
    END RemoveAllType;
  
  PROCEDURE RemoveAllVar (decl: AST.Decl): BOOLEAN;
  (* TRUE iff the whole `VarDecl' starting with `decl' will be removed.  *)
    VAR
      name: AST.IdentDef;
    BEGIN
      REPEAT
        name := decl. name;
        WHILE (name # NIL) DO
          IF (name. name. pos < 0) THEN
            RETURN FALSE
          END;
          name := name. next
        END;
        decl := decl. next
      UNTIL ~(decl IS AST.VarDecl) OR
            (decl(AST.VarDecl). varKW # NIL);
      RETURN TRUE
    END RemoveAllVar;
  
  BEGIN
    (* remove unused import declarations *)
    IF (ast. importList # NIL) THEN
      IF ImportEmpty (ast. importList. imports) THEN
        Remove (ast. importList);
        ast. importList := NIL
        
      ELSE
        decl := ast. importList. imports;
        WHILE (decl # NIL) DO
          next := decl. next;
          WITH decl: AST.Import DO
            IF (decl. name. name. pos > 0) THEN  (* unmarked import *)
              IF (decl. prev = NIL) THEN
                ast. importList. imports := next
              ELSE
                decl. prev. next := next
              END;
              IF (next # NIL) THEN
                next. prev := decl. prev
              END;

              IF (decl. prev # NIL) THEN
                (* ugly hack to keep ascending order when calling `Remove' *)
                Remove (decl. prev(AST.Import). comma);
                decl. prev(AST.Import). comma := decl. comma;
                IF (decl. comma # NIL) THEN
                  decl. comma. up := decl. prev;
                  decl. comma := NIL
                END
              END;
              Remove (decl)
            END
          END;
          decl := next
        END
      END
    END;
    
    (* remove local constant, type, variable, and procedure declarations *)
    decl := ast. body. declSeq;
    WHILE (decl # NIL) DO
      next := decl. next;
      IF (decl. name = NIL) THEN  (* empty CONST, TYPE, VAR *)
        RemoveDecl (decl)
      
      ELSIF (decl IS AST.VarDecl) & Exported (decl. name) THEN  
        (* at least one of the names of the variable declaration is exported *)
        RemoveLocalNames (decl. name);
        ScanDecl (ast, decl, TRUE)
        
      ELSIF (decl. name. name. pos > 0) THEN  (* unmarked declaration *)
        WITH decl: AST.ProcDecl DO
          RemoveDecl (decl)
          
        | decl: AST.ConstDecl DO
          IF (decl. constKW # NIL) & (next # NIL) & (next IS AST.ConstDecl) &
             (next(AST.ConstDecl). constKW = NIL) &
             ~RemoveAllConst (decl) THEN
            (* move keyword CONST over to next declaration *)
            decl. constKW. up := next;
            next(AST.ConstDecl). constKW := decl. constKW;
            decl. constKW := NIL
          END;
          RemoveDecl (decl)
          
        | decl: AST.TypeDecl DO
          IF (decl. typeKW # NIL) & (next # NIL) & (next IS AST.TypeDecl) &
             (next(AST.TypeDecl). typeKW = NIL) &
             ~RemoveAllType (decl) THEN
            (* move keyword TYPE over to next declaration *)
            decl. typeKW. up := next;
            next(AST.TypeDecl). typeKW := decl. typeKW;
            decl. typeKW := NIL
          END;
          RemoveDecl (decl)
        
        | decl: AST.VarDecl DO
          IF (decl. varKW # NIL) & (next # NIL) & (next IS AST.VarDecl) &
             (next(AST.VarDecl). varKW = NIL) &
             ~RemoveAllVar (decl) THEN
            (* move keyword VAR over to next declaration *)
            decl. varKW. up := next;
            next(AST.VarDecl). varKW := decl. varKW;
            decl. varKW := NIL
          END;
          RemoveDecl (decl)
        END
      
      ELSIF (decl IS AST.ProcDecl) THEN
        ScanDecl (ast, decl, TRUE);
        RemoveProcBody (decl(AST.ProcDecl))
      
      ELSE
        ScanDecl (ast, decl, TRUE)
      END;
      decl := next
    END;
    
    (* remove most of the module body, but keep the END symbol *)
    IF (ast. body. begin # NIL) THEN
      Remove (ast. body. begin);
      ast. body. begin := NIL;
      statm := ast. body. statmSeq;
      WHILE (statm # NIL) DO
        nextStatm := statm. next;
        Remove (statm);
        statm := nextStatm
      END;
      ast. body. statmSeq := NIL
    END
  END RemoveLocalDecl;


PROCEDURE Extract* (ast: AST.Module);
(* Trim the syntax tree down to the public interface of the module.  All
   statements are discarded from the tree, as well as all declarations that
   do not contribute to an exported entity.  *)
  VAR
    foundDocString: BOOLEAN;
    
  PROCEDURE ClearMarkers (sym: S.Symbol);
    BEGIN
      WHILE (sym # NIL) DO
        IF (sym. id = S.ident) & (sym. pos < 0) THEN
          sym. NegatePos()
        END;
        sym := sym. next
      END
    END ClearMarkers;
  
  BEGIN
    (* discard all pragmas and (maybe) all normal comments *)
    RemoveComments (ast, foundDocString);
    
    (* mark all declarations that contribute to the module's public
       interface and get rid of local record fields *)
    MarkInterface (ast);
    
    (* remove all unmarked declarations *)
    lastRemoved := NIL;
    RemoveLocalDecl (ast);
    lastRemoved := NIL;
    
    (* remove markers on declarations *)
    ClearMarkers (ast. startSymbol. next)
  END Extract;

END CNModuleDef.
