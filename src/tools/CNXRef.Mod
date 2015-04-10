(*	$Id: CNXRef.Mod,v 1.13 2000/04/22 15:02:56 ooc-devel Exp $	*)
MODULE CNXRef;
(*  Creates cross-reference tables in HTML format.
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
  TextRider, Strings, IntStr, Out, Channel, 
  S := CNScanner, AST := CNAST, SymTab := CNSymTab, Parser := CNParser,
  Modules := CNModules, Decl := CNDecl, Identifier := CNIdentifier,
  HTML := CNHTML, Output := CNOutput, ModuleDef := CNModuleDef, 
  Filter := CNFilter, ScanFile := CNScanFile;


TYPE
  UseRecord = RECORD
    scope: SymTab.Object;
    pos: LONGINT;
  END;
  UsesArray = POINTER TO ARRAY OF UseRecord;
  
  UseInfo = POINTER TO UseInfoDesc;
  UseInfoDesc = RECORD
    (S.InfoDesc)
    href, name: S.String;
    useCount: LONGINT;
    uses: UsesArray;
  END;

  
PROCEDURE SetWriter* (writer: TextRider.Writer);
  BEGIN
    HTML.SetWriter (writer)
  END SetWriter;


PROCEDURE CollectUseInfo (ast: AST.Module);
  VAR
    sym: S.Symbol;
    
  PROCEDURE AddUseInfo (obj: SymTab.Object);
    VAR
      id: ARRAY 1024 OF CHAR;
      useInfo: UseInfo;
      oldCurrModule: AST.Module;
    
    PROCEDURE GenName (obj: SymTab.Object);
      VAR
        procDecl: AST.ProcDecl;

      PROCEDURE WriteNodes (node: AST.Node);
        BEGIN
          IF ~(node IS AST.Scope) THEN
            WriteNodes (node. up);
            IF (node IS AST.Decl) THEN
              Strings.Append (node(AST.Decl). name. name. str^, id);
              Strings.Append (".", id)
            END
          END
        END WriteNodes;

      BEGIN
        IF (obj. mode = SymTab.objField) THEN
          WriteNodes (obj. identDef. up. up)
        ELSIF (obj. mode = SymTab.objTBProc) THEN
          procDecl := obj. identDef. up(AST.ProcDecl);
          WriteNodes (Decl.BaseRecord (procDecl))
        ELSIF (obj. mode = SymTab.objProc) & 
              (obj. localTo(SymTab.Object). mode # SymTab.objModule) THEN
          GenName (obj. localTo(SymTab.Object));
          Strings.Append (".", id)
        END;
        Strings.Append (obj. name^, id)
      END GenName;

    BEGIN
      IF (obj. info = NIL) OR ~(obj. info IS UseInfo) THEN
        NEW (useInfo);
        useInfo. useCount := 0;
        useInfo. uses := NIL;
        
        IF (obj. identDef = NIL) THEN  (* predefined identifier *)
          useInfo. href := NIL
        ELSE
          oldCurrModule := Decl.currModule;
          Decl.currModule := NIL;
          Decl.DeclarationID (obj. identDef, "_", id);
          Decl.currModule := oldCurrModule;
          NEW (useInfo. href, Strings.Length (id)+1);
          COPY (id, useInfo. href^)
        END;
        
        id := "";
        GenName (obj);
        NEW (useInfo. name, Strings.Length (id)+1);
        COPY (id, useInfo. name^);
        
        obj. info := useInfo
      END
    END AddUseInfo;
  
  PROCEDURE AddUse (use: AST.Ident);
    CONST
      offset = 1;
    VAR
      obj, scope: SymTab.Object;
      i: LONGINT;
      new: UsesArray;
      node: AST.Node;
      uinfo: UseInfo;
    BEGIN
      ASSERT (~(use IS AST.IdentDef) OR
              (use. up IS AST.Import) & (use. up(AST.Import). module = use));
      IF (use. obj # NIL) THEN  (* some identifiers are purely decorative *)
        obj := use. obj(SymTab.Object);
        AddUseInfo (obj);
        uinfo := obj. info(UseInfo);

        IF (uinfo. uses = NIL) THEN
          NEW (uinfo. uses, 8-offset);
          FOR i := 0 TO 8-(offset+1) DO
            uinfo. uses[i]. scope := NIL;
            uinfo. uses[i]. pos := 0
          END
        ELSIF (uinfo. useCount = LEN (uinfo. uses^)) THEN
          NEW (new, uinfo. useCount*2+offset);
          FOR i := 0 TO uinfo. useCount-1 DO
            new[i] := uinfo. uses[i];
            uinfo. uses[i]. scope := NIL;
            uinfo. uses[i]. pos := 0
          END;
          FOR i := uinfo. useCount TO LEN (new^)-1 DO
            new[i]. scope := NIL;
            new[i]. pos := 0
          END;
          uinfo. uses := new
        END;

        node := use;
        WHILE ~(node IS AST.Scope) DO
          node := node. up
        END;
        scope := node(AST.Scope). name. obj(SymTab.Object);
        uinfo. uses[uinfo. useCount]. scope := scope;
        uinfo. uses[uinfo. useCount]. pos := use. name. pos;
        INC (uinfo. useCount);
        
        obj. RemoveUse (use)
      END
    END AddUse;
  
  BEGIN
    sym := ast. startSymbol. next;
    WHILE (sym # NIL) DO
      IF (sym. id = S.ident) THEN
        IF (sym. up IS AST.IdentDef) THEN
          AddUseInfo (sym. up(AST.IdentDef). obj(SymTab.Object));
          
          IF (sym. up. up IS AST.Import) &
             (sym. up. up(AST.Import). becomes = NIL) THEN
            (* record identifier added by the parser for an IMPORT without
               an alias name *)
            AddUse (sym. up. up(AST.Import). module)
          END
        ELSIF (sym. up IS AST.Ident) THEN
          AddUse (sym. up(AST.Ident))
        (* ELSE: (sym. up IS AST.FlagList) *)
        END
      END;
      sym := sym. next
    END
  END CollectUseInfo;


PROCEDURE WriteObject (obj: SymTab.Object; selectProc: BOOLEAN; 
                       indent: INTEGER; defOnly: BOOLEAN);
  VAR
    str: ARRAY 16 OF CHAR;
    tag: SHORTINT;
    uinfo: UseInfo;
    i: LONGINT;

  PROCEDURE WriteFields (struct: SymTab.Struct; obj: SymTab.Object;
                        selectProc: BOOLEAN);
    VAR
      member: SymTab.Object;
    BEGIN
      IF (struct. form # SymTab.strUndef) &
         ((struct. obj = NIL) OR (struct. obj = obj)) THEN
        IF (struct. form = SymTab.strRecord) THEN
          member := struct. decl;
          WHILE (member # NIL) DO
            IF ((member. mode = SymTab.objTBProc) = selectProc) THEN
              WriteObject (member, selectProc, indent+2, defOnly)
            END;
            member := member. rightObj
          END
        ELSIF (struct. base # NIL) THEN
          WriteFields (struct. base,  NIL, selectProc)
        END
      END
    END WriteFields;
  
  PROCEDURE WriteScope (scope: SymTab.Object; 
                        selectProc, selectFields: BOOLEAN;
                        indent: INTEGER);
    VAR
      obj:  SymTab.Object;
      
    PROCEDURE WriteTree (obj: SymTab.Object);
      BEGIN
        IF (obj # NIL) THEN
          WriteTree (obj. leftObj);
          IF (obj. mode # SymTab.objModule) THEN
            IF selectFields THEN
              IF (obj. type # NIL) THEN
                WriteFields (obj. type, obj, selectProc)
              END
            ELSIF (selectProc = (obj. mode = SymTab.objProc)) THEN
              IF selectProc THEN
                WriteObject (obj, selectProc, 0, defOnly)
              ELSE
                WriteObject (obj, selectProc, indent+2, defOnly)
              END
            END
          END;
          WriteTree (obj. rightObj)
        END
      END WriteTree;

    BEGIN
      IF ~selectProc THEN
        HTML.WriteLn;
        HTML.WriteSpaces (indent);
        HTML.WriteTag ("<UL>")
      END;
      
      IF ~selectProc THEN
        IF (scope. mode = SymTab.objTBProc) THEN
          WriteObject (scope(SymTab.TBProc). receiver, selectProc, indent+2, defOnly)
        END;
        IF (scope. type # NIL) THEN
          obj := scope. type. decl;
          WHILE (obj # NIL) DO
            IF (obj. mode # SymTab.objRestParam) THEN
              WriteObject (obj, selectProc, indent+2, defOnly)
            END;
            obj := obj. rightObj
          END
        END
      END;
      WriteTree (scope. localDecl);
      
      IF ~selectProc THEN
        HTML.WriteLn;
        HTML.WriteSpaces (indent);
        HTML.WriteTag ("</UL>")
      END
    END WriteScope;

  PROCEDURE WriteModule (u: SymTab.Usable; tag: BOOLEAN);
    VAR
      filename: ARRAY 256 OF CHAR;
    BEGIN
      WHILE ~(u IS SymTab.Module) DO
        u := u. localTo
      END;
      COPY (u(SymTab.Module). name^, filename);
      IF tag THEN
        Output.FixModuleName (filename)
      END;
      HTML.WriteText (filename)
    END WriteModule;
  
  PROCEDURE WriteLocation (scope: SymTab.Object);
    VAR
      base: SymTab.Struct;
    BEGIN
      WITH scope: SymTab.Module DO
        HTML.WriteText (scope. name^)
      | scope: SymTab.TBProc DO
        WriteModule (scope. localTo, FALSE);
        HTML.WriteText (".");
        base := SymTab.GetBaseType (scope, TRUE);
        HTML.WriteText (base. obj. name^);
        HTML.WriteText (".");
        HTML.WriteText (scope. name^)
      ELSE (* normal procedure *)
        WriteLocation (scope. localTo(SymTab.Object));
        HTML.WriteText (".");
        HTML.WriteText (scope. name^)
      END
    END WriteLocation;
  
  PROCEDURE WriteUse (msg: ARRAY OF CHAR; VAR use: UseRecord);
    BEGIN
      HTML.WriteLn;
      HTML.WriteSpaces (indent+2);
      HTML.WriteTag ("<LI>");
      HTML.WriteTag (msg);
      HTML.WriteTag ('<A HREF="');
      WriteModule (use. scope, TRUE);
      IF defOnly THEN
        HTML.WriteTag ("_def")
      END;
      HTML.WriteTag (".html#");
      IntStr.IntToStr (use. pos, str);
      HTML.WriteTag (str);
      HTML.WriteTag ('">');
      WriteLocation (use. scope);
      HTML.WriteTag ("</A></LI>");
    END WriteUse;
  
  PROCEDURE WriteInfoHREF (uinfo: UseInfo);
    VAR
      i: INTEGER;
      filename: S.Filename;
    BEGIN
      IF defOnly THEN
        COPY (uinfo. href^, filename);
        i := 0;
        WHILE (filename[i] # ".") DO
          ASSERT (filename[i] # 0X);
          INC (i)
        END;
        Strings.Insert ("_def", i, filename);
        HTML.WriteTag (filename)
      ELSE
        HTML.WriteTag (uinfo. href^)
      END
    END WriteInfoHREF;
  
  PROCEDURE WriteDeclUse (msg: ARRAY OF CHAR; use: SymTab.Object);
    BEGIN
      HTML.WriteLn;
      HTML.WriteSpaces (indent+2);
      HTML.WriteTag ("<LI>");
      HTML.WriteTag (msg);
      HTML.WriteTag ('<A HREF="');
      WriteInfoHREF (use. info(UseInfo));
      HTML.WriteTag ('">');
      WriteLocation (use);
      HTML.WriteTag ("</A></LI>");
    END WriteDeclUse;
  
  PROCEDURE WriteTBProc (obj: SymTab.TBProc);
    VAR
      base: SymTab.TBProc;
    
    PROCEDURE ScanTBUses (baseObj: SymTab.TBProc; record: SymTab.Struct);
      VAR
        member: SymTab.Object;
        ext: SymTab.Struct;
        uinfo: UseInfo;
        i: LONGINT;
      BEGIN
        member := record. decl;
        WHILE (member # NIL) & (member. name^ # baseObj. name^) DO
          member := member. rightObj
        END;
        
        IF (member # NIL) THEN
          IF (member. mode = SymTab.objTBProc) &
             ((member = baseObj) OR 
              SymTab.Redefinition (baseObj, member(SymTab.TBProc))) THEN
            IF (member # baseObj) THEN
              WriteDeclUse ("<EM>Redefinition</EM>: ", member)
            END;
            
            i := 0;
            uinfo := member. info(UseInfo);
            WHILE (i < uinfo. useCount) DO
              WriteUse ("", uinfo. uses[i]);
              INC (i)
            END
          ELSE  (* the local definition is no redefinition of `baseObj' *)
            RETURN
          END
        END;

        ext := record. extList;
        WHILE (ext # NIL) DO
          ScanTBUses (baseObj, ext);
          ext := ext. nextExt
        END
      END ScanTBUses;
    
    BEGIN
      IF (obj. super = NIL) THEN
        (* this is the top-most declaration of the method *)
        ScanTBUses (obj, SymTab.GetBaseType (obj, FALSE))
      ELSE  (* redefinition of an inherited procedure *)
        base := obj;
        WHILE (base. super # NIL) DO
          base := base. super
        END;
        HTML.WriteLn;
        HTML.WriteSpaces (indent+2);
        HTML.WriteTag ('<LI>Base Definition: <A HREF="');
        WriteModule (base, TRUE);
        IF defOnly THEN
          HTML.WriteTag ("_def")
        END;
        HTML.WriteTag ("_xref.html#");
        IntStr.IntToStr (base. pos, str);
        HTML.WriteTag (str);
        HTML.WriteTag ('">');
        WriteLocation (base);
        HTML.WriteTag ("</A></LI>")
      END
    END WriteTBProc;
  
  BEGIN
    IF ~SymTab.ScopeObject (obj) THEN
      HTML.WriteLn;
      HTML.WriteSpaces (indent);
      HTML.WriteTag ("<LI>")
    END;
    
    CASE obj. mode OF
    | SymTab.objModule: tag := HTML.scope; str := "MODULE"
    | SymTab.objProc:   tag := HTML.scope; str := "PROCEDURE"
    | SymTab.objTBProc: tag := HTML.scope; str := "TBPROC"
    | SymTab.objConst:  tag := HTML.keyword; str := "CONST"
    | SymTab.objType:   tag := HTML.keyword; str := "TYPE"
    | SymTab.objVar:
      tag := HTML.keyword;
      IF (SymTab.objIsParameter IN obj. flags) THEN
        str := "PARAM"
      ELSE
        str := "VAR"
      END
    | SymTab.objVarPar: tag := HTML.keyword; str := "PARAM"
    | SymTab.objField:  tag := HTML.keyword; str := "FIELD"
    END;
    IF (tag = HTML.scope) & (obj. mode # SymTab.objModule) THEN
      HTML.WriteTag ("<HR>")
    END;
    
    HTML.WriteLn;
    HTML.WriteSpaces (indent);
    HTML.WriteTag ("<TT>");
    HTML.WriteTag (HTML.startTag[tag]);
    HTML.WriteText (str);
    HTML.WriteTag (HTML.endTag[tag]);
    HTML.WriteTag (" </TT>");
    IF (SymTab.objIsExported IN obj. flags) THEN
      HTML.WriteTag (HTML.startTag[HTML.export])
    END;
    
    HTML.WriteTag ('<A HREF="');
    WriteInfoHREF (obj. info(UseInfo));
    HTML.WriteTag ('" NAME="');
    IntStr.IntToStr (obj. pos, str);
    HTML.WriteTag (str);
    HTML.WriteTag ('">');
    HTML.WriteText (obj. info(UseInfo). name^);
    HTML.WriteTag ("</A>");
    IF (SymTab.objIsExported IN obj. flags) THEN
      HTML.WriteTag (HTML.endTag[HTML.export])
    END;
    
    HTML.WriteLn;
    HTML.WriteSpaces (indent);
    HTML.WriteTag ("<UL>");
    IF (obj. mode = SymTab.objTBProc) THEN
      WriteTBProc (obj(SymTab.TBProc))
    ELSE  (* write standard use list *)
      uinfo := obj. info(UseInfo);
      i := 0;
      WHILE (i < uinfo. useCount) DO
        WriteUse ("", uinfo. uses[i]);
        INC (i)
      END
    END;
    HTML.WriteLn;
    HTML.WriteSpaces (indent);
    HTML.WriteTag ("</UL>");
    
    IF (obj. type # NIL) THEN
      WriteFields (obj. type, obj, FALSE)
    END;
    
    IF SymTab.ScopeObject (obj) THEN
      WriteScope (obj, FALSE, FALSE, indent);
      IF (obj. mode = SymTab.objModule) THEN
        WriteScope (obj, TRUE, TRUE, indent)
      END;
      WriteScope (obj, TRUE, FALSE, indent)
    ELSE
      HTML.WriteLn;
      HTML.WriteSpaces (indent);
      HTML.WriteTag ("</LI>")
    END;
  END WriteObject;

PROCEDURE ScanModules (modList: Modules.ModuleList;
                       writeHTML, defOnly, lineNum: BOOLEAN;
                       filter: Filter.Set): SymTab.Object;
  VAR
    moduleList: SymTab.Object;
    mod: Modules.ModuleList;
    ch: Channel.Channel;
    mobj: SymTab.Module;
    
  PROCEDURE ScanModule (VAR name: ARRAY OF CHAR; 
                        VAR moduleList: SymTab.Object): SymTab.Module;
    VAR
      list: S.StartSymbol;
      module: AST.Module;
      filename: S.Filename;
      mobj: SymTab.Module;
    BEGIN
      Modules.LocateModule (name, filename);

      list := ScanFile.Scan (filename);
      S.Abs2Rel (list);
      module := Parser.ParseModule (list);
      Filter.Apply (module. startSymbol, filter);
      IF defOnly THEN
        ModuleDef.Extract (module)
      END;
      mobj := SymTab.CreateSymTab (module, moduleList);
      Identifier.CreateUseLists (module, moduleList);
      
      Decl.CacheModule (module);
      S.ClearStringTable;

      mobj. rightObj := moduleList;
      moduleList := mobj;
      RETURN mobj
    END ScanModule;

  BEGIN
    moduleList := NIL;
    Decl.FlushCache;
    mod := modList;
    WHILE (mod # NIL) DO
      IF ~Modules.InternalModule (mod. module. name^) THEN
        mobj := ScanModule (mod. module. name^, moduleList);
        
        IF writeHTML THEN
          IF defOnly THEN
            ch := Output.Open (mod. module. name^, "_def", "html");
            HTML.SetWriter (TextRider.ConnectWriter (ch));
            HTML.WriteSymbols (mobj. ast, "_def", TRUE, lineNum)
          ELSE
            ch := Output.Open (mod. module. name^, "", "html");
            HTML.SetWriter (TextRider.ConnectWriter (ch));
            HTML.WriteSymbols (mobj. ast, "", TRUE, lineNum)
          END;
          Output.Close (ch)
        END;
        
        CollectUseInfo (mobj. ast);
        (* unfortunately the module `CNHTML.Mod' depends on parts of imported
           syntax trees to build the hyperlinks for record fields and type-
           bound procedures, or we could discard the whole AST; as it
           is, we can only remove the private parts *)
        Decl.RemoveLocal (mobj. ast)
      END;
      mod := mod. next
    END;
    
    RETURN moduleList
  END ScanModules;

PROCEDURE XRefModule (module: SymTab.Module; defOnly: BOOLEAN);
  VAR
    ch: Channel.Channel;
  
  PROCEDURE WriteHead;
    BEGIN
      HTML.WriteTag ("<HTML>"); HTML.WriteLn;
      HTML.WriteTag ("<HEAD>"); HTML.WriteLn;
      HTML.WriteTag ("<TITLE>");
      HTML.WriteText (module. name^);
      HTML.WriteTag ("</TITLE>"); HTML.WriteLn;
      HTML.WriteTag ("</HEAD>"); HTML.WriteLn;
      HTML.WriteTag ('<BODY BGCOLOR="#FFFAFA" TEXT="#000000" LINK="#000000" VLINK="#000000">'); HTML.WriteLn
    END WriteHead;
  
  PROCEDURE WriteTail;
    BEGIN
      HTML.WriteTag ("</BODY>"); HTML.WriteLn;
      HTML.WriteTag ("</HTML>"); HTML.WriteLn
    END WriteTail;
  
  BEGIN
    IF defOnly THEN
      ch := Output.Open (module. name^, "_def_xref", "html")
    ELSE
      ch := Output.Open (module. name^, "_xref", "html")
    END;
    SetWriter (TextRider.ConnectWriter (ch));

    WriteHead;
    WriteObject (module, FALSE, 0, defOnly);
    WriteTail;
    Output.Close (ch)
  END XRefModule;

PROCEDURE WriteXRef* (modList: Modules.ModuleList; defOnly, lineNum: BOOLEAN;
                      filter: Filter.Set);
(* defOnly=TRUE: only write public interface of module
   lineNum=TRUE: include line numbers in HTML file *)
  VAR
    moduleList: SymTab.Object;
    modSymTab: SymTab.Object;
  BEGIN
    moduleList := ScanModules (modList, TRUE, defOnly, lineNum, filter);
    moduleList := SymTab.Reverse (moduleList);

    modSymTab := moduleList;
    WHILE (modSymTab # NIL) DO
      Decl.currModule := NIL;  (* force absolute HTML HREF strings *)
      XRefModule (modSymTab(SymTab.Module), defOnly);
      modSymTab := modSymTab. rightObj
    END
  END WriteXRef;

PROCEDURE WriteUses* (modList: Modules.ModuleList; declName: ARRAY OF CHAR);
  VAR
    id: ARRAY 1024 OF CHAR;
    len, pos, start: INTEGER;
    curr: SymTab.Usable;
    type: SymTab.Struct;
    moduleList, mod, obj: SymTab.Object;
    tbProc: SymTab.TBProc;
  
  PROCEDURE WriteFile (obj: SymTab.Object): BOOLEAN;
  (* result is FALSE if `obj' is part of a pseudo module *)
    VAR
      u: SymTab.Usable;
    BEGIN
      u := obj;
      WHILE ~(u IS SymTab.Module) DO
        u := u. localTo
      END;
      IF (u(SymTab.Module). ast = NIL) THEN
        RETURN FALSE
      ELSIF (u(SymTab.Module). ast. startSymbol. file^ # id) THEN
        COPY (u(SymTab.Module). ast. startSymbol. file^, id);
        Out.String ("In file ");
        Out.String (id);
        Out.String (": ");
        Out.Ln
      END;
      RETURN TRUE
    END WriteFile;
  
  PROCEDURE WriteDecl (obj: SymTab.Object);
    BEGIN
      IF WriteFile (obj) THEN
        Out.LongInt (obj. pos, 0);
        Out.String (": declaration");
        Out.Ln
      END
    END WriteDecl;
  
  PROCEDURE ListUses (uinfo: UseInfo);
    VAR
      i: LONGINT;
    BEGIN
      i := 0;
      WHILE (i # uinfo. useCount) DO
        IF WriteFile (uinfo. uses[i]. scope) THEN
          Out.LongInt (uinfo. uses[i]. pos, 0);
          Out.String (": use");
          Out.Ln
        END;
        INC (i)
      END
    END ListUses;
  
  PROCEDURE WriteTBUses (baseObj: SymTab.TBProc; record: SymTab.Struct);
    VAR
      member: SymTab.Object;
      ext: SymTab.Struct;
      dummy: BOOLEAN;
    BEGIN
      member := record. decl;
      WHILE (member # NIL) & (member. name^ # baseObj. name^) DO
        member := member. rightObj
      END;

      IF (member # NIL) THEN
        IF (member. mode = SymTab.objTBProc) &
           ((member = baseObj) OR 
            SymTab.Redefinition (baseObj, member(SymTab.TBProc))) THEN
          dummy := WriteFile (member);
          Out.LongInt (member. pos, 0);
          IF (member = baseObj) THEN
            Out.String (": base definition")
          ELSE
            Out.String (": redefinition")
          END;
          Out.Ln;
          ListUses (member. info(UseInfo))
        ELSE  (* the local definition is no redefinition of `baseObj' *)
          RETURN
        END
      END;

      ext := record. extList;
      WHILE (ext # NIL) DO
        WriteTBUses (baseObj, ext);
        ext := ext. nextExt
      END
    END WriteTBUses;

  BEGIN
    moduleList := ScanModules (modList, FALSE, FALSE, FALSE, Filter.noOperation);
    moduleList := SymTab.Reverse (moduleList);
    
    len := Strings.Length (declName);
    pos := 0;
    curr := NIL;
    WHILE (pos < len) DO
      start := pos;
      WHILE (pos # len) & (declName[pos] # 0X) & (declName[pos] # ".") DO
        INC (pos)
      END;
      Strings.Extract (declName, start, pos-start, id);

      IF (curr = NIL) THEN  (* looking for module or predefined object *)
        IF (id = "SYSTEM") THEN
          curr := SymTab.system
        ELSE
          mod := moduleList;
          WHILE (curr = NIL) & (mod # NIL) DO
            IF (mod. name^ = id) THEN
              curr := mod
            END;
            mod := mod. rightObj
          END
        END;
        
        IF (curr = NIL) THEN
          (* the string does not match any module name, maybe it's a
             predefined name *)
          curr := SymTab.Find (SymTab.predef, id)
        END
      ELSIF (curr IS SymTab.Object) & 
            SymTab.ScopeObject (curr(SymTab.Object)) THEN
        (* looking for declaration *)
        curr := SymTab.Find (curr(SymTab.Object), id)
      ELSE  (* looking for record field *)
        type := curr(SymTab.Object). type;
        WHILE (type # NIL) & (type. form # SymTab.strRecord) DO
          type := type. base
        END;
        IF (type = NIL) THEN
          curr := NIL
        ELSE
          curr := SymTab.FindDecl (type, id)
        END
      END;
      
      IF (curr = NIL) THEN
        IF (start = 0) THEN
          Out.String ("Error: Unknown module `")
        ELSE
          Out.String ("Error: Unknown declaration `")
        END;
        declName[pos] := 0X;
        Out.String (declName);
        Out.String ("'");
        Out.Ln;
        HALT (1)
      ELSIF (declName[pos] = ".") THEN
        INC (pos)
      END
    END;
    
    id := "";
    IF (curr IS SymTab.TBProc) THEN
      tbProc := curr(SymTab.TBProc);
      WHILE (tbProc. super # NIL) DO
        tbProc := tbProc. super
      END;
      WriteTBUses (tbProc, SymTab.GetBaseType (tbProc, FALSE))
    ELSE
      obj := curr(SymTab.Object);
      WriteDecl (obj);
      ListUses (obj. info(UseInfo))
    END
  END WriteUses;


BEGIN
  SetWriter (NIL)
END CNXRef.
