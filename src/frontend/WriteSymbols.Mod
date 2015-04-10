(* 	$Id: WriteSymbols.Mod,v 1.9 1999/03/07 09:45:03 acken Exp $	 *)
MODULE WriteSymbols;  (* Copyright (C) 1995-1999  Michael van Acken *)

IMPORT
  Out, Strings, IntStr, LRealStr, D := Data, Sym := SymbolTable;

CONST
  writeIDs = TRUE;
  
  
PROCEDURE Ln (off: INTEGER);
  VAR
    i: INTEGER;
  BEGIN
    Out.Ln;
    FOR i := 1 TO off DO
      Out.String ("  ")
    END
  END Ln;


PROCEDURE Const* (const: D.Const; VAR str: ARRAY OF CHAR);
  PROCEDURE Char (char: LONGINT);
    VAR
      i: INTEGER;
      
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
        COPY ("' '", str); str[1] := '"'
      ELSIF (char < ORD (" ")) OR (char = 7FH) OR
            (char > ORD (MAX (CHAR))) THEN
        COPY ("0xxxxX", str);
        FOR i := 4 TO 1 DO
          str[i] := Cypher (char MOD 16);
          char := char DIV 16
        END;
        WHILE (str[0] = "0") & (str[1] < "A") DO
          Strings.Delete (str, 0, 1)
        END
      ELSE
        COPY ('" "', str); str[1] := CHR (char)
      END
    END Char; 
    
  PROCEDURE Real (val: LONGREAL; prec: INTEGER; exp: CHAR);
    VAR
      i: SHORTINT;
    BEGIN
      LRealStr.RealToFloat (val, prec, str);
      i := 0;
      WHILE (str[i] # 0X) & (str[i] # "E") DO
        INC (i)
      END;
      IF (str[i] = "E") THEN
        str[i] := exp
      ELSIF (exp = "D") THEN
        Strings.Append ("D0", str)
      END
    END Real;
  
  PROCEDURE Set (set: SET);
    VAR
      i: INTEGER;
      sep: BOOLEAN;
      num: ARRAY 32 OF CHAR;
    BEGIN
      COPY ("{", str);
      sep := FALSE; i := 0;
      WHILE (i <= MAX (SET)) DO
        IF (i IN set) THEN
          IF sep THEN
            Strings.Append (", ", str)
          END;
          IntStr.IntToStr (i, num);
          Strings.Append (num, str);
          IF (i+2 <= MAX (SET)) & (i+1 IN set) & (i+2 IN set) THEN
            WHILE (i+1 <= MAX (SET)) & (i+1 IN set) DO
              INC (i)
            END;
            Strings.Append ("..", str);
            IntStr.IntToStr (i, str);
            Strings.Append (num, str)
          END;
          sep := TRUE
        END;
        INC (i)
      END;
      Strings.Append ("}", str)
    END Set;
  
  PROCEDURE String8 (s: ARRAY OF CHAR; len: LONGINT);
    VAR
      ch: CHAR;
      i: INTEGER;
    BEGIN
      (* determine string delimiter *)
      ch := '"';
      i := 0;
      WHILE (s[i] # 0X) & (s[i] # '"') DO
        INC (i)
      END;
      IF (s[i] # 0X) THEN
        ch := "'"
      END;
      (* write string *)
      str[0] := ch; str[1] := ch; str[2] := 0X;
      Strings.Insert (s, 1, str)
    END String8;
  
  PROCEDURE String16 (s: ARRAY OF CHAR; len: LONGINT);
    BEGIN  (* emit just a placeholder for the moment... *)
      COPY ("__long_string__", str)
    END String16;
  
  BEGIN
    CASE const. type. form OF
    | D.strBoolean:
      IF (const. int = 0) THEN
        COPY ("FALSE", str)
      ELSE
        COPY ("TRUE", str)
      END
    | D.strChar8, D.strChar16:
      Char (const. int)
    | D.strShortInt..(D.strReal-1):
      IntStr.IntToStr (const. int, str)
    | D.strReal:
      Real (const. real, 7, "E")
    | D.strLongReal:
      Real (const. real, 14, "D")
    | D.strSet8..D.strSet64:
      Set (const. set)
    | D.strStringConst8:
      String8 (const. string^, const. int)
    | D.strStringConst16:
      String16 (const. string^, const. int)
    | D.strNil:
      COPY ("NIL", str)
    | D.strUndef:
      COPY ("undef_const", str)
    END
  END Const;

PROCEDURE WriteConst* (const: D.Const);
  VAR
    str: ARRAY 256 OF CHAR;
  BEGIN
    Const (const, str);
    Out.String (str)
  END WriteConst;

PROCEDURE WriteTree (obj: D.Object; off: INTEGER);
  PROCEDURE WriteObject (obj: D.Object);
    PROCEDURE WriteStruct (t: D.Struct; structure: BOOLEAN; off: INTEGER);
      VAR
        mod, obj: D.Object;
      BEGIN
        IF (t. obj = NIL) OR structure THEN
          CASE t. form OF
          | D.strUndef: 
            Out.String ("_undef struct_")
          | D.strStringConst8:
            Out.String ("_string8_")
          | D.strStringConst16:
            Out.String ("_string16_")
          | D.strNil:
            Out.String ("_nil_")
          | D.strNone:
            Out.String ("_no type_")
          | D.strPointer:
            Out.String ("POINTER TO "); WriteStruct (t. base, FALSE, off)
          | D.strProc:
            IF structure THEN
              Out.String ("PROCEDURE")
            END;
            IF (t. decl # NIL) OR (t. base. form # D.strNone) THEN
              Out.String (" (");
              obj := t. decl;
              WHILE (obj # NIL) DO
                IF (obj # t. decl) THEN
                  Out.String ("; ")
                END;
                WriteObject (obj);
                obj := obj. rightObj
              END;
              Out.Char (")");
              IF (t. base. form # D.strNone) THEN
                Out.String (": ");
                WriteStruct (t. base, FALSE, off)
              END
            END
          | D.strArray:
            Out.String ("ARRAY ");
            Out.LongInt (t. len, 0);
            Out.String (" OF ");
            WriteStruct (t. base, FALSE, off)
          | D.strOpenArray:
            Out.String ("ARRAY OF ");
            WriteStruct (t. base, FALSE, off)
          | D.strRecord:
            Out.String ("RECORD");
            IF (t. base # NIL) THEN
              Ln (off); 
              Out.Char ("("); 
              WriteStruct (t. base, FALSE, off);
              Out.Char (")")
            END;
            obj := t. decl;
            WHILE (obj # NIL) DO
              Ln (off);
              WriteObject (obj);
              obj := obj. rightObj
            END;
            Ln (off-1); Out.String ("END")
          END
        ELSE
          mod := Sym.Module (t. obj);
          IF (mod # Sym.predef) THEN
            Out.String (mod. data(D.Const). string^);
            Out.Char (".")
          END;
          Out.String (t. obj. name^)
        END
      END WriteStruct;
    
    PROCEDURE Name;
      BEGIN
        IF (obj. name = NIL) OR (obj. name^ = "") THEN
          Out.String ("_no name_")
        ELSE
          Out.String (obj. name^)
        END;
        IF (D.objIsExported IN obj. flags) THEN
          IF (D.objIsExportedReadOnly IN obj. flags) THEN
            Out.Char ("-")
          ELSE
            Out.Char ("*")
          END
        END
      END Name;
    
    BEGIN
      IF writeIDs THEN    
        Out.String ("[mid="); Out.Int (obj. moduleId, 0);
        Out.String (",lev="); Out.Int (obj. level, 0);
        Out.String ("] ")
      END;
      CASE obj. mode OF
      | D.objUndef:
        Out.String ("_undef object_")
      | D.objConst: 
        Out.String ("CONST "); Name; 
        Out.String (" = "); WriteConst (obj. data(D.Const))
      | D.objType:
        Out.String ("TYPE "); Name; Out.String (" = "); 
        WriteStruct (obj. type, obj. type. obj = obj, off+1)
      | D.objVar:
        Out.String ("VAR "); Name; Out.String (": "); 
        WriteStruct (obj. type, FALSE, off+1)
      | D.objVarPar:
        Out.String ("VARPAR "); Name; Out.String (": "); 
        WriteStruct (obj. type, FALSE, off+1)
      | D.objField:
        Name; Out.String (": "); 
        WriteStruct (obj. type, FALSE, off+1)
      | D.objProc, D.objTBProc:
        Out.String ("PROCEDURE ");
        IF (obj. data # NIL) THEN
          Out.Char ("(");
          WriteObject (obj. data(D.Object));
          Out.String (") ")
        END;
        Name;
        WriteStruct (obj. type, FALSE, off+1);
        WriteTree (obj. localDecl, off+1)
      | D.objModule:
        Out.String ("IMPORT "); Out.String (obj. name^); Out.String (" := ");
        Out.String (obj. data(D.Const). string^)
      | D.objRestParam:
        Out.String ("...")
      END
    END WriteObject;
  
  BEGIN
    IF (obj # NIL) THEN
      WriteTree (obj. leftObj, off);
      Ln (off); Ln (off);
      WriteObject (obj);
      WriteTree (obj. rightObj, off)
    END
  END WriteTree;

PROCEDURE WriteModule* (mod: D.Object);
  VAR
    obj: D.Object;
  BEGIN
    Out.String ("MODULE ");
    Out.String (mod. name^);
    IF (mod. data # NIL) THEN
      Out.String (", FILE ");
      Out.String (mod. data(D.Const). string^)
    END;
    IF writeIDs THEN
      Out.String (" [mid="); Out.Int (mod. moduleId, 0);
      Out.String (",lev="); Out.Int (mod. level, 0);
      Out.String ("]")
    END;
    Out.Ln; Out.Ln;
    (* list of imports (only present when read from symbol file) *)
    Out.String ("Module.left:");
    obj := mod. leftObj;
    WHILE (obj # NIL) DO
      Out.Char (" ");
      Out.String (obj. data(D.Const). string^);
      obj := obj. rightObj
    END;
    Out.Ln; Out.Ln;

    (* write objects in module's visibility scope *)
    WriteTree (mod. localDecl, 0);
    
    Out.Ln; Out.Ln;
    Out.String ("END ");
    IF (mod. data = NIL) THEN
      Out.String (mod. name^)
    ELSE
      Out.String (mod. data(D.Const). string^)
    END;
    Out.Char (".");
    Out.Ln
  END WriteModule;

END WriteSymbols.
