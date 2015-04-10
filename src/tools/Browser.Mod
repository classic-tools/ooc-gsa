(* 	$Id: Browser.Mod,v 1.17 1999/03/04 18:45:27 acken Exp $	 *)
MODULE Browser;
(*  Implements symbol file browser.
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
  Out, Strings, LRealStr, Options := ParamOptions,
  D := Data, Sym := SymbolTable;


CONST
  objIsMarked = D.objIsForwardDecl;
  
VAR
  extendedFormat-: Options.BooleanOption;
  
  browseMod: D.Object;
  
  
PROCEDURE Ln (off: INTEGER);
(* Writes newline and indents the next line. *)
  VAR
    i: INTEGER;
  BEGIN
    Out.Ln;
    FOR i := 1 TO off DO
      Out.String ("  ")
    END
  END Ln;


PROCEDURE ^ WriteStruct (t: D.Struct; structure, procPrefix: BOOLEAN; off: INTEGER);

PROCEDURE WriteConst (const: D.Const);
(* Writes constant value. *)
  PROCEDURE WriteChar (char: LONGINT);
    VAR
      i: INTEGER;
      num: ARRAY 64 OF CHAR;
      
    PROCEDURE Cypher (int: LONGINT): CHAR;
      BEGIN
        IF (int < 10) THEN
          RETURN CHR (int + ORD ("0"))
        ELSE
          RETURN CHR (int - 10 + ORD ("A"))
        END
      END Cypher;
    
    BEGIN
      IF (char = ORD ('"')) THEN
        Out.Char ("'"); Out.Char ('"'); Out.Char ("'")
      ELSIF (char < ORD (" ")) OR (char = 127) OR (char > 255) THEN
        num := "0xxxxX";
        FOR i := 4 TO 1 DO
          num[i] := Cypher (char MOD 16);
          char := char DIV 16
        END;
        WHILE (num[0] = "0") & (num[1] < "A") DO
          Strings.Delete (num, 0, 1)
        END;
        Out.String (num)
      ELSE
        Out.Char ('"'); Out.Char (CHR (char)); Out.Char ('"')
      END
    END WriteChar; 
    
  PROCEDURE WriteReal (val: LONGREAL; prec: INTEGER; exp: CHAR);
    VAR
      i: SHORTINT;
      num: ARRAY 64 OF CHAR;
    BEGIN
      LRealStr.RealToFloat (val, prec, num);
      i := 0;
      WHILE (num[i] # 0X) & (num[i] # "E") DO
        INC (i)
      END;
      IF (num[i] = "E") THEN
        num[i] := exp
      ELSIF (exp = "D") THEN
        Strings.Append ("D0", num)
      END;
      Out.String (num)
    END WriteReal;
  
  PROCEDURE WriteSet (set: SET);
    VAR
      i: INTEGER;
      sep: BOOLEAN;
    BEGIN
      Out.Char ("{");
      sep := FALSE; i := 0;
      WHILE (i <= MAX (SET)) DO
        IF (i IN set) THEN
          IF sep THEN
            Out.String (", ")
          END;
          Out.Int (i, 0);
          IF (i+2 <= MAX (SET)) & (i+1 IN set) & (i+2 IN set) THEN
            WHILE (i+1 <= MAX (SET)) & (i+1 IN set) DO
              INC (i)
            END;
            Out.String ("..");
            Out.Int (i, 0)
          END;
          sep := TRUE
        END;
        INC (i)
      END;
      Out.Char ("}")
    END WriteSet;
  
  PROCEDURE WriteString8 (str: ARRAY OF CHAR; len: LONGINT);
    VAR
      ch: CHAR;
      i: LONGINT;
    BEGIN
      (* determine string delimiter *)
      ch := '"';
      i := 0;
      WHILE (i # len) & (str[i] # '"') DO
        INC (i)
      END;
      IF (i # len) THEN
        ch := "'"
      END;
      (* write string *)
      Out.Char (ch); Out.String (str); Out.Char (ch)
    END WriteString8;
  
  PROCEDURE WriteString16 (str: ARRAY OF CHAR; len: LONGINT);
    BEGIN
      Out.String ('"__long_string__"')
    END WriteString16;
  
  BEGIN
    CASE const. type. form OF
    | D.strBoolean:
      IF (const. int = 0) THEN
        Out.String ("FALSE")
      ELSE
        Out.String ("TRUE")
      END
    | D.strChar8, D.strChar16:
      WriteChar (const. int)
    | D.strShortInt..D.strLongInt:
      Out.LongInt (const. int, 0)
    | D.strReal:
      WriteReal (const. real, 9, "E")
    | D.strLongReal:
      WriteReal (const. real, 17, "D")
    | D.strSet8..D.strSet64:
      WriteSet (const. set)
    | D.strStringConst8:
      WriteString8 (const. string^, const^. int)
    | D.strStringConst16:
      WriteString16 (const. string^, const^. int)
    | D.strNil:
      Out.String ("NIL")
    END
  END WriteConst;

PROCEDURE ImplicitExport (obj: D.Object): BOOLEAN;
  BEGIN
    RETURN (obj. mode = D.objType) &
           ~(D.objIsExported IN obj. flags)
  END ImplicitExport;

PROCEDURE IdentDef (obj: D.Object);
(* Writes `obj's name and adds export mark.  *)
  BEGIN
    IF (obj. name = NIL) OR (obj. name^ = "") THEN
      Out.String ("_no name_")
    ELSIF ImplicitExport (obj) THEN
      Out.Char ("[");
      Out.String (obj. name^);
      Out.Char ("]")
    ELSE
      Out.String (obj. name^)
    END;
    IF (D.objIsExported IN obj. flags) &
       (D.objIsExportedReadOnly IN obj. flags) THEN
      Out.Char ("-")
    END
  END IdentDef;

PROCEDURE WriteObject (obj: D.Object; off: INTEGER);
(* Writes a constant, type, variable, variable parameter, or procedure 
   object. *)
  BEGIN
    IF (obj. mode = D.objVarPar) THEN  (* receiver object *)
      Out.String ("VAR ")
    END;
    IdentDef (obj);
    CASE obj. mode OF
    | D.objConst: 
      Out.String (" = "); 
      WriteConst (obj. data(D.Const))
    | D.objType:
      Out.String (" = "); 
      WriteStruct (obj. type, obj. type. obj = obj, TRUE, off)
    | D.objVar, D.objVarPar:
      Out.String (": "); 
      WriteStruct (obj. type, FALSE, TRUE, off)
    | D.objProc:
      WriteStruct (obj. type, FALSE, FALSE, off)
    END
  END WriteObject;

PROCEDURE WriteObjectList (VAR ptr: D.Object);
(* Writes list of names that is part of a formal parameter list or that 
   contains some record fields.  Entries that share the same mode and the same
   unnamed type are collected into a list.
   pre: `ptr' is the start of the list, `ptr' isn't NIL
   post: `ptr' is the element just behind the list *)
  VAR
    end: D.Object;
  BEGIN
    end := ptr;
    REPEAT
      end := end. rightObj
    UNTIL (end = NIL) OR (end. mode # ptr. mode) OR 
          (end. type # ptr. type) OR (ptr. type. obj # NIL);
    IdentDef (ptr);
    ptr := ptr. rightObj;
    WHILE (ptr # end) DO
      Out.String (", ");
      IdentDef (ptr);
      ptr := ptr. rightObj
    END
  END WriteObjectList;

PROCEDURE WriteStruct (t: D.Struct; structure, procPrefix: BOOLEAN; off: INTEGER);
(* Writes type `t'.  If `structure=TRUE', write the type structure even if the
   type is named.  With `procPrefix=TRUE' write the symbol "PROCEDURE" before 
   any procedure types (ie, before the formal parameter list).  `off' is the 
   indentation level of the declaration as part of which this type is 
   written.  *)
  VAR
    mod, obj: D.Object;
    form: INTEGER;
    name: ARRAY 64 OF CHAR;
    
  PROCEDURE WriteProc (t: D.Struct);
  (* Writes formal parameter list `t', possibly prefixed by "PROCEDURE".  *)
    VAR
      head: D.Object;
    BEGIN
      IF procPrefix THEN
        Out.String ("PROCEDURE")
      END;
      IF (t. decl # NIL) OR (t. base. form # D.strNone) THEN
        Out.String (" (");
        obj := t. decl;
        WHILE (obj # NIL) DO
          IF (obj # t. decl) THEN
            Out.String ("; ")
          END;
          IF (obj. mode = D.objRestParam) THEN
            Out.String ("...");
            obj := obj. rightObj
          ELSE
            head := obj;
            IF (head. mode = D.objVarPar) THEN
              Out.String ("VAR ")
            END;
            WriteObjectList (obj);
            Out.String (": ");
            WriteStruct (head. type, FALSE, TRUE, off)
          END
        END;
        Out.Char (")");
        IF (t. base. form # D.strNone) THEN
          Out.String (": ");
          WriteStruct (t. base, FALSE, TRUE, off)
        END
      END
    END WriteProc;
  
  PROCEDURE WriteRecord (t: D.Struct);
  (* Writes record type `t', `extendedFormat. true' determines if the details
     of base types of extended records are part of the record description.  *)
  
    PROCEDURE WriteLocalContents (declList: D.Object);
      VAR
        first, wroteField: BOOLEAN;
        obj, head: D.Object;
      BEGIN
        wroteField := FALSE;
        (* write record fields *)
        first := TRUE; 
        obj := declList;
        WHILE (obj # NIL) DO
          IF (obj. mode = D.objField) & (D.objIsExported IN obj. flags) THEN
            IF ~first THEN
              Out.Char (";")
            ELSE
              first := FALSE
            END;
            Ln (off);
            head := obj;
            WriteObjectList (obj);
            Out.String (": ");
            WriteStruct (head. type, FALSE, TRUE, off);
            wroteField := TRUE
          ELSE
            obj := obj. rightObj
          END
        END;
        (* write type-bound procedures *)
        first := TRUE; obj := declList;
        WHILE (obj # NIL) DO
          IF (obj. mode = D.objTBProc) & (D.objIsExported IN obj. flags) THEN
            IF first THEN
              IF wroteField THEN
                Ln (off)
              END;
              first := FALSE
            END;
            Ln (off);
            Out.String ("PROCEDURE ");
            Out.Char ("(");
            WriteObject (obj. data(D.Object), off);
            Out.String (") ");
            IdentDef (obj);
            WriteStruct (obj. type, FALSE, FALSE, off);
            Out.Char (";")
          END;
          obj := obj. rightObj
        END
      END WriteLocalContents;
    
    PROCEDURE WriteBaseTypes (list: D.Struct);
      BEGIN
        IF (list. base # NIL) THEN
          WriteBaseTypes (list. base);
          Ln (off)
        END;
        Ln (off);
        Out.String ("(* ");
        WriteStruct (list, FALSE, TRUE, 0);
        Out.String (" *)");
        WriteLocalContents (list. decl);
      END WriteBaseTypes;
      
    BEGIN
      Out.String ("RECORD");
      INC (off);
      (* write base type(s) *)
      IF (t. base # NIL) THEN
        IF extendedFormat. true THEN
          WriteBaseTypes (t)
        ELSE
          Ln (off); 
          Out.Char ("("); 
          WriteStruct (t. base, FALSE, TRUE, off);
          Out.Char (")");
          (* write record fields and type-bound procedures *)
          WriteLocalContents (t. decl)
        END
      ELSE
        WriteLocalContents (t. decl)
      END;
      DEC (off);
      Ln (off); 
      Out.String ("END")
    END WriteRecord;
  
  BEGIN
    form := t. form;
    IF (D.strUndef < form) & (form <= D.strNone) THEN
      (* predefined types are atomic *)
      Out.String (t. obj. name^)
    ELSIF (form < D.strPointer) OR (form > D.strRecord) THEN
      (* this type id represents a group of type; this can happen if we are
         writing the type of a predefined procedure's parameter *)
      Sym.TypeName (name, t);
      Out.String (name)
    ELSIF (t. obj = NIL) OR structure THEN
      CASE form OF
      | D.strPointer:
        Out.String ("POINTER TO "); WriteStruct (t. base, FALSE, TRUE, off)
      | D.strProc:
        WriteProc (t)
      | D.strArray:
        Out.String ("ARRAY ");
        Out.LongInt (t. len, 0);
        WHILE (t. base. form = D.strArray) DO
          Out.String (", ");
          t := t. base;
          Out.LongInt (t. len, 0)
        END;
        Out.String (" OF ");
        WriteStruct (t. base, FALSE, TRUE, off)
      | D.strOpenArray:
        Out.String ("ARRAY OF ");
        WriteStruct (t. base, FALSE, TRUE, off)
      | D.strRecord:
        WriteRecord (t)
      END
    ELSE
      mod := Sym.Module (t. obj);
      IF (mod # Sym.predef) & (mod. name^ # browseMod. name^) THEN
        Out.String (mod. data(D.Const). string^);
        Out.Char (".")
      END;
      Out.String (t. obj. name^)
    END
  END WriteStruct;

PROCEDURE WriteObjects (root: D.Object; mode: SHORTINT);
  VAR
    first: BOOLEAN;
    
  PROCEDURE WriteTree (obj: D.Object);
    VAR
      firstVar: BOOLEAN;
      
    PROCEDURE WriteVarList (ptr: D.Object);
      BEGIN
        IF (ptr # NIL) THEN
          WriteVarList (ptr. leftObj);
          IF (ptr. mode = D.objVar) & (ptr. type = obj. type) THEN
            IF firstVar THEN
              firstVar := FALSE
            ELSE
              Out.String (", ")
            END;
            IdentDef (ptr);
            INCL (ptr. flags, objIsMarked)
          END;
          WriteVarList (ptr. rightObj)
        END
      END WriteVarList;
    
    BEGIN
      IF (obj # NIL) THEN
        WriteTree (obj. leftObj);
        IF (obj. mode = mode) & 
           ((D.objIsExported IN obj. flags) OR ImplicitExport (obj)) &
           ~(objIsMarked IN obj. flags) THEN
          (* the current object has the correct mode, is exported by its module
             and hasn't been written previously *)
          (* write mode prefix *)
          IF first THEN
            Ln (0);
            CASE mode OF
            | D.objConst: 
              Ln (0); Out.String ("CONST");
            | D.objType:
              Ln (0); Out.String ("TYPE")
            | D.objVar:
              Ln (0); Out.String ("VAR")
            | D.objProc:
              Ln (0)
            END
          END;
          IF (mode = D.objProc) THEN
            Ln (0);
            Out.String ("PROCEDURE ")
          ELSE
            Ln (1)
          END;
          IF (mode = D.objVar) & (obj. type. obj = NIL) THEN
            (* collect unnamed variables of same type into a single list *)
            firstVar := TRUE;
            WriteVarList (root);
            Out.String (": ");
            WriteStruct (obj. type, FALSE, TRUE, 1)
          ELSE
            INCL (obj. flags, objIsMarked);
            WriteObject (obj, 1)
          END;
          Out.Char (";");
          first := FALSE
        END;
        WriteTree (obj. rightObj)
      END
    END WriteTree;
  
  BEGIN
    first := TRUE;
    WriteTree (root)
  END WriteObjects;


PROCEDURE WriteModule* (mod: D.Object);
(* pre: `mod' has been imported with `ReadSymbolFile' *)
  VAR
    obj: D.Object;
  
  PROCEDURE Unmark (obj: D.Object);
    BEGIN
      IF (obj # NIL) THEN
        Unmark (obj. leftObj);
        Unmark (obj. rightObj);
        EXCL (obj. flags, objIsMarked)
      END
    END Unmark;
  
  BEGIN
    browseMod := mod;
    IF extendedFormat. true THEN
      Out.String ("EXTENDED ")
    END;
    Out.String ("MODULE ");
    Out.String (mod. data(D.Const). string^);
    Out.Char (";");
    (* list of imports (only present when read from symbol file) *)
    IF (mod. leftObj # NIL) THEN
      Ln (0); Ln (0);
      Out.String ("IMPORT");
      Ln (1);
      obj := mod. leftObj;
      WHILE (obj # NIL) DO
        IF (obj # mod. leftObj) THEN
          Out.String (", ")
        END;
        Out.String (obj. data(D.Const). string^);
        obj := obj. rightObj
      END;
      Out.Char (";");
      Out.Ln
    END;

    (* write objects in module's visibility scope *)
    WriteObjects (mod. localDecl, D.objConst);
    WriteObjects (mod. localDecl, D.objType);
    WriteObjects (mod. localDecl, D.objVar);
    WriteObjects (mod. localDecl, D.objProc);
    
    Ln (0); Ln (0);
    Out.String ("END ");
    Out.String (mod. data(D.Const). string^);
    Out.Char (".");
    Ln (0);
    browseMod := NIL
  END WriteModule;

BEGIN
  extendedFormat := Options.CreateBoolean ("browseExtended", FALSE);
  Options.options. Add (extendedFormat);
  Options.options. CmdLineOption ("-x,--extended", "browseExtended:=TRUE")
END Browser.
