(*	$Id: LocText.Mod,v 1.6 1999/10/31 13:54:00 ooc-devel Exp $	*)
MODULE LocText;

(*
    LocText - text string localization facilities.
    Copyright (C) 1997 Michael Griebling
 
    This module is free software; you can redistribute it and/or modify
    it under the terms of the GNU Lesser General Public License as 
    published by the Free Software Foundation; either version 2 of the
    License, or (at your option) any later version.
 
    This module is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Lesser General Public License for more details.
 
    You should have received a copy of the GNU Lesser General Public
    License along with this program; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

*)

IMPORT Files, IntStr, tr:=TextRider, Out, 
       l:=Locales, Filenames, s:=Strings, Channel, Msg;

CONST
  DEBUG = FALSE;
  IdentLength = 30;
  DefDir = "lib/locales";   (* system default catalog directory *)
  
  ErrPrefix = "+++";        (* error prefix string *)
  
  (* local error codes *)
  noError*             = Channel.done;
  expectingEOL*        = -100;
  expectingString*     = expectingEOL-1;
  expectingName*       = expectingString-1;
  wrongEndName*        = expectingName-1;
  expectingEnd*        = wrongEndName-1;
  expectingSecItemCom* = expectingEnd-1;
  catalogNotFound*     = expectingSecItemCom-1;
  masterNotFound*      = catalogNotFound-1;
  expectingCatalog*    = masterNotFound-1;
  expectingSysLocale*  = expectingCatalog-1;
  expectingLocaleCom*  = expectingSysLocale-1;
  masterIsEmpty*       = expectingLocaleCom-1;
  sectionNotFound*     = masterIsEmpty-1;
  catalogIsEmpty*      = sectionNotFound-1;
  duplicateEntry*      = catalogIsEmpty-1;

TYPE
  Ident = ARRAY IdentLength OF CHAR;
  String = POINTER TO ARRAY OF CHAR;
  
(*************************************************************
 *
 * Error return values.
 *
 *)
  ErrDesc* = RECORD
    err-: Msg.Msg;     (* error code *)
    pos-: LONGINT;     (* char position in file at error *)
    fname-: tr.String; (* name of the file *)
  END;
  
(*************************************************************
 *
 * Entries in a catalog
 *
 *)
  Node = POINTER TO NodeDesc;          (* basic type -- placeholder *)  
  Section * = POINTER TO SectionDesc; (* catalog section *)  
  Item = POINTER TO ItemDesc;         (* catalog item *)  
  NodeDesc = RECORD
    ident: Ident;   (* identifying label *)
    next: Node      (* next entry *)
  END;
  SectionDesc * = RECORD(NodeDesc)
    list: Node
  END;
  ItemDesc = RECORD(NodeDesc)
    item: String
  END;
  
(*************************************************************
 *
 * Locale items from the master index
 *
 *)
  Locale* = RECORD
    locale-, catalog-, syslocale-: String;
    include: Section
  END;
  Locales = POINTER TO RECORD
    loc: POINTER TO ARRAY OF Locale;  (* list of locales *)  
    dir: String;                      (* base directory *)
    path: String                      (* possible paths *)
  END;  
  
VAR
  dbase-: Section;   (* global database *)

      
TYPE
  ErrorContext = POINTER TO ErrorContextDesc;
  ErrorContextDesc = RECORD
    (Channel.ErrorContextDesc)
  END;

VAR
  errorContext: ErrorContext;

PROCEDURE GetError (code: Msg.Code): Msg.Msg;
  BEGIN
    RETURN Msg.New (errorContext, code)
  END GetError;



PROCEDURE ^ (sec: Section) Get * (selector: ARRAY OF CHAR; VAR str: ARRAY OF CHAR); (* forward *)
PROCEDURE ^ (sec: Section) GetSelector * (VAR selector: ARRAY OF CHAR);

      
(*************************************************************
 *
 * Error handling routines
 *
 *)  
 
PROCEDURE ErrorDescr * (err: ErrDesc; VAR descr: ARRAY OF CHAR);
(* 
   No localization for errors since, if there's an
   error, we probably can't read the catalog file
   anyway. 
 *)
VAR
  str: ARRAY 256 OF CHAR; 
BEGIN
  (* copy default error message *)
  CASE err.err.code OF
  | expectingEOL        : str := "Expecting an <EOL>"
  | expectingString     : str := "Expecting a string"
  | expectingName       : str := "Expecting a name"
  | wrongEndName        : str := "Mismatched names at section END"
  | expectingEnd        : str := "Expecting an `END'"
  | expectingSecItemCom : str := "Expecting a `SECTION', `@', String, or `#'"
  | catalogNotFound     : str := "Catalog file was not found"
  | catalogIsEmpty      : str := "Catalog file was empty or not loaded"
  | masterNotFound      : str := "Master file was not found"
  | masterIsEmpty       : str := "Master file was empty or not loaded"
  | sectionNotFound     : str := "Section was not found"
  | expectingCatalog    : str := "Expecting a `CATALOG'"
  | expectingSysLocale  : str := "Expecting a `SYSLOCALE'"
  | expectingLocaleCom  : str := "Expecting a `LOCALE' or `#'"
  | duplicateEntry      : str := "Duplicate named item or section"
  | ELSE                  str := "Unknown error code"
  END;
  COPY(str, descr); s.Append(" at pos=", descr);
  IntStr.IntToStr(err.pos, str); s.Append(str, descr);
  s.Append(" in file ", descr); s.Append(err.fname, descr)
END ErrorDescr;

PROCEDURE IsError * (str: ARRAY OF CHAR) : BOOLEAN;
(* Return TRUE iff `str' is an error string (i.e., prefixed by `+++') *)
VAR
  pos: INTEGER; found: BOOLEAN;
BEGIN
  s.FindNext(ErrPrefix, str, 0, found, pos);
  RETURN found & (pos=0)
END IsError;

PROCEDURE (sec: Section) MakeErrorStr (selector: ARRAY OF CHAR; VAR errStr: ARRAY OF CHAR);
BEGIN
  sec.GetSelector(errStr); s.Insert(ErrPrefix, 0, errStr);
  IF selector#"" THEN s.Append(".", errStr); s.Append(selector, errStr) END
END MakeErrorStr;

PROCEDURE (sec: Section) MakeErrorIndex (selector: ARRAY OF CHAR; index: LONGINT; VAR errStr: ARRAY OF CHAR);
BEGIN
  IntStr.IntToStr(index, errStr);
  
  sec.GetSelector(errStr); s.Insert(ErrPrefix, 0, errStr);
  IF selector#"" THEN s.Append(".", errStr); s.Append(selector, errStr) END
END MakeErrorIndex;

PROCEDURE ExpErrorDescr (selector: ARRAY OF CHAR; VAR descr: ARRAY OF CHAR);
(* 
    Exported error localization for modules called by LocText. 
 *)
BEGIN
  IF dbase#NIL THEN dbase.Get(selector, descr)
  ELSE COPY(selector, descr) 
  END
END ExpErrorDescr;

PROCEDURE Error (VAR err: ErrDesc; errNum: LONGINT; fname: ARRAY OF CHAR; pos: LONGINT);
BEGIN
  IF err.err#noError THEN RETURN END;
  err.err:=GetError (errNum); err.pos:=pos; COPY(fname, err.fname)
END Error;

PROCEDURE ClearError (VAR err: ErrDesc);
BEGIN
  err.err:=noError; err.pos:=0; err.fname:=""
END ClearError;

(*************************************************************
 *
 * Database manipulation routines
 *
 *)

PROCEDURE Init (VAR dbase: Section);
BEGIN
  NEW(dbase);      (* create an empty section head *)
  dbase.ident:="";
  dbase.next:=NIL; (* field is not used at top level *)
  dbase.list:=NIL; (* top-level sections are added here *)
END Init;

PROCEDURE (sec: Section) Find (id: ARRAY OF CHAR): Node;
(* return a locale item for a given id; NIL if not found *)
VAR
  node: Node; sid: Ident; pos: INTEGER; found: BOOLEAN;
BEGIN
  (* empty id indicates this section *)
  IF id="" THEN RETURN sec END;
  
  (* find the item within the locale base *)
  LOOP
    s.FindNext(".", id, 0, found, pos);
    IF found THEN
      s.Extract(id, 0, pos, sid);
      s.Delete(id, 0, pos+1)
    ELSE COPY(id, sid)
    END;
   
    (* look through the contained sections *)
    node:=sec.list;    
    WHILE (node#NIL) & (sid#node.ident) DO node:=node.next END;
    
    (* determine what was found -- if anything *)
    IF (node=NIL) OR ~found THEN
      (* no matching item found or no further selectors *)
      RETURN node
    ELSIF node IS Section THEN 
      (* matching section found and selectors are left *)
      sec:=node(Section)
    ELSE 
      (* found an item, but need a section *)
      RETURN NIL
    END
  END  
END Find;

PROCEDURE (sec: Section) GetSelector * (VAR selector: ARRAY OF CHAR);
(*
  Return the selector string which would return section `sec'.
*)
  
  PROCEDURE GetName (r: Section; VAR selector: ARRAY OF CHAR) : BOOLEAN;
  (* return `selector' which would find `sec' relative to `r' *)
  VAR
    node: Node; 
  BEGIN
    IF r=sec THEN COPY(r.ident, selector); RETURN TRUE
    ELSE (* check if sec is in r's domain *)
      node:=r.list;
      WHILE node#NIL DO
        IF (node IS Section) & GetName(node(Section), selector) THEN
          IF r.ident#"" THEN
            s.Insert(".", 0, selector); 
            s.Insert(r.ident, 0, selector)
          END;
          RETURN TRUE
        END;
        node:=node.next 
      END
    END;
    RETURN FALSE
  END GetName;
  
BEGIN
  IF ~GetName(dbase, selector) THEN
    COPY("", selector)
  END
END GetSelector;

PROCEDURE (sec: Section) Get * (selector: ARRAY OF CHAR; VAR str: ARRAY OF CHAR);
(* 
   Return the text string in `str' for the `selector' which is relative 
   to section `s'.  If no such item exists `str' will be set to the
   value of "+++" + <s selector> + "." + `selector'.  For example,
   assuming s = section "menubar", selector="filemenu.e1.name" would 
   return the string "Open..." from the example shown in ReadCatalog.
*)
VAR
  loc: Node;
BEGIN
  loc:=sec.Find(selector);
  IF (loc#NIL) & (loc IS Item) THEN COPY(loc(Item).item^, str)
  ELSE sec.MakeErrorStr(selector, str)
  END
END Get;

PROCEDURE (sec: Section) GetElement * (selector: ARRAY OF CHAR; index: LONGINT; 
                                       VAR str: ARRAY OF CHAR);
(* 
   Return the `index' element of the section selected by `selector' which is 
   relative to section `s' into `str'.  An empty selector selects the `index'
   element of `s'.  If no such item exists `str' will be set to the value:
   "+++" + <s selector> + ["." + <selector>] + "." + <index>.  For example, 
   in section s="weekdays", selector="" and index=1 would return str="Monday" 
   from the example in ReadCatalog. 
*)
VAR
  loc: Node;
BEGIN
  (* find the requested section *)
  loc:=sec.Find(selector);
  IF (loc=NIL) OR (loc IS Item) THEN sec.MakeErrorIndex(selector, index, str); RETURN END;
  
  (* locate the `id'th element of that section *)
  loc:=loc(Section).list;
  WHILE (index>0) & (loc#NIL) DO loc:=loc.next; DEC(index) END;
  
  (* return the found element *)
  IF (loc#NIL) & (loc IS Item) THEN COPY(loc(Item).item^, str)
  ELSE sec.MakeErrorIndex(selector, index, str)
  END
END GetElement;

PROCEDURE (sec: Section) GetSection * (selector: ARRAY OF CHAR) : Section;
(* 
   Return the section for the `selector' which is relative to
   section `sec'.  If the selector does not exist or if it is
   an empty string, `sec' will be returned. 
 *)
VAR
  loc: Node;
BEGIN
  (* attempt to locate the section *)
  loc:=sec.Find(selector);
  IF (loc=NIL) OR (loc IS Item) THEN RETURN sec  
  ELSE RETURN loc(Section)
  END  
END GetSection;


(*************************************************************
 *
 * Utility routines to build the database
 *
 *)  

PROCEDURE (sec: Section) AddSection (value: Node; VAR err: ErrDesc);
VAR
  node, p: Node;
BEGIN
  (* check for duplicate sections *)
  p:=NIL; node:=sec.list;
  WHILE (node#NIL) & (value.ident#node.ident) DO p:=node; node:=node.next END;
  
  (* insert an item only if it is new *)
  IF p=NIL THEN sec.list:=value ELSE p.next:=value END; 
  IF node=NIL THEN value.next:=NIL                  (* add a section at the end *)
  ELSIF node IS Section THEN value.next:=node.next  (* replace section contents *) 
  ELSE Error(err, duplicateEntry, value.ident, 0)   (* item exists with section name *)
  END
END AddSection;

PROCEDURE (sec: Section) AddItem (id, value: ARRAY OF CHAR; VAR err: ErrDesc);
VAR
  node, p: Node; item: Item;
BEGIN
  (* check for duplicate items *)
  p:=NIL; node:=sec.list;
  WHILE (node#NIL) & (id#node.ident) DO p:=node; node:=node.next END;
  
  (* insert an item only if it is new *) 
  IF node=NIL THEN (* add an item at the end *)
    NEW(item); COPY(id, item.ident); 
    NEW(item.item, s.Length(value)+1); COPY(value, item.item^);
    IF p=NIL THEN sec.list:=item ELSE p.next:=item END; 
    item.next:=NIL
  ELSE Error(err, duplicateEntry, id, 0) (* duplicate item *)
  END
END AddItem;

PROCEDURE Comment (fname: ARRAY OF CHAR; sin: tr.Scanner; VAR err: ErrDesc);
VAR line: LONGINT; prev: SET;
BEGIN
  (* check for comments *)
  line:=sin.lines;

  (* ignore strings within comments *)
  prev:=sin.opt;
  sin.SetOpts(sin.opt-{tr.interpretStrings});
  
  (* skip to next line *)
  REPEAT sin.Scan;
  UNTIL (sin.lines#line) OR 
        (sin.type IN {tr.error, tr.invalid});
  IF sin.type IN {tr.error, tr.invalid} THEN
    Error(err, expectingEOL, fname, sin.pos)
  END;
 
  (* enable string reading again *)
  sin.SetOpts(prev)
END Comment;

PROCEDURE ReadCatalog (cat: Section; file: Files.File; fname: ARRAY OF CHAR; VAR err: ErrDesc);
(* This routine reads an external catalog `fname' into `cat' with 
   the following syntax:
   
   catalog    = entry_list
   entry_list = {section | item | string}
   comment    = "#" {char} "<eol>"
   section    = "SECTION" ident entry_list "END" ident
   item       = "@" ident string
   filename   = Oberon2_string
   string     = Oberon2_string {"+" Oberon2_string}
   
   where ident is a valid Oberon-2 identifier with a maximum
   length of 30 characters and a string consists of one or more
   valid Oberon-2 strings which are concatenated up to a maximum
   length of 2000 characters.  Identifiers must be unique 
   within a section.  Strings occuring in an entry_list are an 
   abbreviation for:
   
      @ n string
      
   where `n' is an automatically assigned integer identifier
   which starts at 0 and is numbered sequentially for all
   strings within a section.  `err' returns the error code
   associated with attempting to open and read the catalog.
   An empty section is an error.
   
   An example of a valid locale definition follows:
   
   SECTION menubar
     SECTION filemenu
       @ name "File";
       SECTION e1
         @ name      "Open..."
         @ shortcut  "Alt-O"
         @ shorthelp "Open a file"
       END e1
       # .. more entries
     END filemenu
     # ... more menu bar entries
   END menubar
   
   SECTION weekdays
     "Sunday"   -- an automatic label "0" is created
     "Monday"   -- an automatic label "1" is created
     "Tuesday"  -- an automatic label "2" is created
     "And a " +
     "multiline " +
     "string"
     -- etc.
   END weekdays
*)
VAR
  sin: tr.Scanner;
  
  PROCEDURE EntryList (entry: Section; cnt: LONGINT);
  
    PROCEDURE GetString (VAR str: ARRAY OF CHAR);
    BEGIN
      sin.Scan;
      WHILE (sin.type=tr.char) & (sin.char="+") DO
        sin.Scan;
        IF sin.type=tr.string THEN 
          s.Append(sin.string, str); sin.Scan
        ELSE 
          Error(err, expectingString, fname, sin.pos); RETURN
        END
      END
    END GetString;

    PROCEDURE AddItem (entry: Section);
    VAR
      id: Ident; str: ARRAY 2048 OF CHAR;
    BEGIN
      sin.Scan;
      IF sin.type=tr.ident THEN
        COPY(sin.string, id);   (* get the item name *)
        sin.Scan;
        IF sin.type=tr.string THEN
          COPY(sin.string, str);
          GetString(str);        (* get a concatenated string *)
          entry.AddItem(id, str, err)
        ELSE Error(err, expectingString, fname, sin.pos)
        END
      ELSE Error(err, expectingName, fname, sin.pos)
      END
    END AddItem;
    
    PROCEDURE AddNumberItem (VAR id: LONGINT; entry: Section);
    VAR
      idstr: Ident; str: ARRAY 2048 OF CHAR;
    BEGIN
      COPY(sin.string, str);
      IntStr.IntToStr(id, idstr); INC(id); 
      GetString(str);          (* get a concatenated string *)
      entry.AddItem(idstr, str, err)
    END AddNumberItem;    
    
    PROCEDURE AddSection (entry: Section);
    VAR
      sec: Section; cnt: LONGINT; 
    BEGIN
      sin.Scan; Init(sec); cnt:=0;
      IF sin.type=tr.ident THEN
        COPY(sin.string, sec.ident);  (* get the section name *)
        EntryList(sec, cnt);          (* and the contents *)
        IF (sin.type=tr.ident) & (sin.string="END") THEN
          sin.Scan;
          IF (sin.type=tr.ident) & (sin.string=sec.ident) THEN
            entry.AddSection(sec, err)
          ELSE Error(err, wrongEndName, fname, sin.pos)
          END
        ELSE Error(err, expectingEnd, fname, sin.pos)
        END
      ELSE Error(err, expectingName, fname, sin.pos)
      END;
      sin.Scan
    END AddSection;
      
  BEGIN
    sin.Scan;
    REPEAT
      IF (sin.type=tr.ident) & (sin.string="SECTION") THEN AddSection(entry)
      ELSIF sin.type=tr.string THEN AddNumberItem(cnt, entry)
      ELSIF (sin.type=tr.char) & (sin.char="#") THEN Comment(fname, sin, err)
      ELSIF (sin.type=tr.char) & (sin.char="@") THEN AddItem(entry) 
      ELSE Error(err, expectingSecItemCom, fname, sin.pos)
      END
    UNTIL (err.err#noError) OR (sin.type IN {tr.error, tr.invalid}) OR
          ((sin.type=tr.ident) & (sin.string="END"))
  END EntryList;
  
BEGIN   
  (* open the catalog file *)
  sin:=tr.ConnectScanner(file);
  IF sin=NIL THEN RETURN END;
  
  (* allow `+' use for concatenation *)
  sin.SetOpts(sin.opt-{tr.useSignedNumbers});  
  
  (* parse the file *)
  ClearError(err);
  EntryList(cat, 0)
END ReadCatalog;


(*************************************************************
 *
 * Master file and catalog input/output routines.
 *
 *)  

PROCEDURE SetLocale * (locList: Locales; locName: ARRAY OF CHAR; VAR err: ErrDesc);
(* 
   Reads and activates the catalog file of the specified language. 
   An appropriate error code, the error position in the file and
   the filename are returned in `err' for any error conditions.
   Calls Locales.Set when required.  In case of an error the old 
   locale setting remains in effect.
*)
VAR
  cnt: LONGINT; old, fname: tr.String; 
  file: Files.File;
  ptr: Node;
  
  PROCEDURE Open (name : ARRAY OF CHAR) : Files.File;
  (* search through all directories until the `name' is found *)
  VAR
    path: tr.String;
    pos: INTEGER; found: BOOLEAN;
    status: Msg.Msg;
    file: Files.File;
  BEGIN
    (* first look through the "PATH" directories *)
    COPY(locList.path^, path);
    WHILE path[0]#0X DO
      s.FindNext(":", path, 0, found, pos);
      IF found THEN s.Extract(path, 0, pos, fname); s.Delete(path, 0, pos+1)
      ELSE fname:=path; path:=""
      END;
      
      (* check if paths are relative to base directory *)
      Filenames.ExpandPath(fname, fname);
      IF fname="" THEN COPY(locList.dir^, fname)
      ELSIF fname[0]="." THEN
        s.Delete(fname, 0, 1);
        Filenames.AddPath(fname, locList.dir^, fname)
      END;
      
      (* attempt to open the file *)
      Filenames.AddPath(fname, fname, name);
      file:=Files.Old(fname, {Files.read}, status);
      IF file#NIL THEN RETURN file END;        
    END;
    
    (* then look in the system default directory *)
    Filenames.AddPath(fname, DefDir, name);
    file:=Files.Old(fname, {Files.read}, status);
    IF file#NIL THEN RETURN file END;      
    
    (* finally look in the base directory *)
    Filenames.AddPath(fname, locList.dir^, name); 
    RETURN Files.Old(fname, {Files.read}, status)  
  END Open;
    
BEGIN
  (* verify that locName is a valid locale *)
  ClearError(err);
  cnt:=0;
  IF locList.loc=NIL THEN 
    Error(err, masterIsEmpty, "", 0); RETURN 
  END;
  WHILE (cnt<LEN(locList.loc^)) & (locList.loc[cnt].locale^#locName) DO
    INC(cnt)
  END;
  
  (* open the external catalog *)
  IF cnt=LEN(locList.loc^) THEN  
    Error(err, sectionNotFound, locName, 0); RETURN 
  END; 
  file:=Open(locList.loc[cnt].catalog^);
  IF file=NIL THEN 
    Error(err, catalogNotFound, fname, 0); RETURN 
  END;
  ReadCatalog(dbase, file, fname, err);
  file.Close;
  
  (* open other related catalogs *)
  IF locList.loc[cnt].include#NIL THEN
    ptr:=locList.loc[cnt].include.list;
    WHILE ptr#NIL DO
      IF ptr IS Item THEN 
        file:=Open(ptr(Item).item^);
        IF file#NIL THEN ReadCatalog(dbase, file, fname, err) END
      END;
      ptr:=ptr.next
    END
  END;
  IF dbase.list=NIL THEN RETURN END;  (* nothing was read *)
  
  (* set the appropriate locale *)
  IF locList.loc[cnt].syslocale^="" THEN (* nothing is set *) 
  ELSIF locList.loc[cnt].syslocale^="setenv" THEN l.Set(l.ALL, "", old)
  ELSE l.Set(l.ALL, locList.loc[cnt].syslocale^, old)
  END
END SetLocale;

PROCEDURE ReadLocales * (file: ARRAY OF CHAR; VAR locList: Locales; VAR err: ErrDesc);
(* 
   Get the supported locales for the current program from the master file
   specified by `file'.  NIL is returned in `LocList' for any errors.  The
   `err' values will reflect the error status.  This file is expected 
   to contain a list of all the localization catalog names for a given 
   program.  The entries in this file are expected with the following syntax: 
 
   Master file = [path] {locale}
   path        = "PATH" string
   locale      = "LOCALE" string  
                   "CATALOG" filename 
                   "SYSLOCALE" string
                   ["INCLUDE" filename {"," filename}]
   filename    = string
   
   and string is a valid Oberon-2 string.  The first string following
   "LOCALE" is the name of the locale.  The corresponding catalog file
   name (interpreted relative to the master file location), and the
   final string is fed to Locales.Set(ALL, string).  If the last string
   is empty, Locales.Set isn't called; if it is "setenv", then
   Locales.Set(ALL, "") is called.  The string following "PATH" is
   a list of directories separated by `:'s which are searched in the
   order specified for all the catalog files.  Relative names in "PATH"
   (e.g., beginning with "." or empty strings) are interpreted relative
   to the location of the master file.  If no match is found, the
   search continues in the system's default locales directory located
   at %DEFLOCDIR%. 
   
   An example of this master file is shown below:
   
   PATH "/usr/lib/ooc/loc:/usr/lib/ooc/vo/loc"
   LOCALE "Deutsch (Deutschland)" 
     CATALOG   "de.cat" 
     SYSLOCALE "de_DE"
     INCLUDE   "ooc_de.cat"
   LOCALE "Deutsch (Schweiz)"     
     CATALOG   "de.cat" 
     SYSLOCALE "de_CH"
     INCLUDE   "ooc_de.cat"
   LOCALE "Deutsch (Ostereich)"   
     CATALOG   "de.cat" 
     SYSLOCALE "de_AU"
     INCLUDE   "ooc_de.cat"
   LOCALE "default"               
     CATALOG   "en.cat" 
     SYSLOCALE ""
     INCLUDE   "ooc_en.cat"
   
   Based on the entries in this file, the following catalog files
   will be expected in the same directory where the master file is
   found or in one of the "PATH" directories:
   
     de.cat
     en.cat
     ooc_de.cat
     ooc_en.cat
*)
TYPE
  ptr=POINTER TO ptrDesc;
  ptrDesc=RECORD (Locale)
    next: ptr
  END;
VAR
  loc: ptr;
  f: Files.File;
  sc: tr.Scanner;
  dir, name, path: tr.String;
  cnt, total: LONGINT;
  status: Msg.Msg;
  
  PROCEDURE AddLocale (VAR l:ptr; item: ptr);
  VAR
    node, p: ptr;
  BEGIN
    (* go to the last entry *)
    p:=NIL; node:=l;
    WHILE node#NIL DO p:=node; node:=node.next END;
    
    (* insert an item at the end *)
    IF p=NIL THEN l:=item ELSE p.next:=item END;
    item.next:=NIL;
    INC(total)
  END AddLocale;  
    
  PROCEDURE Check (token: ARRAY OF CHAR; VAR res: String): BOOLEAN;
  BEGIN
    sc.Scan;
    IF (sc.type=tr.ident) & (sc.string=token) THEN
      sc.Scan;
      IF sc.type=tr.string THEN 
        NEW(res, s.Length(sc.string)+1); COPY(sc.string, res^)
      ELSE Error(err, expectingString, file, sc.pos)
      END
    ELSIF token="CATALOG" THEN Error(err, expectingCatalog, file, sc.pos)
    ELSIF token="SYSLOCALE" THEN Error(err, expectingSysLocale, file, sc.pos)
    END;
    RETURN err.err=noError
  END Check;
    
  PROCEDURE GetLocale (VAR loc: ptr);
  VAR
    item: ptr; id: LONGINT; idstr: ARRAY 32 OF CHAR;
  BEGIN
    sc.Scan; NEW(item); id:=0;
    item.include:=NIL;
    IF sc.type=tr.string THEN 
      NEW(item.locale, s.Length(sc.string)+1);
      COPY(sc.string, item.locale^);
      IF Check("CATALOG", item.catalog) & Check("SYSLOCALE", item.syslocale) THEN
        sc.Scan;
        IF (sc.type=tr.ident) & (sc.string="INCLUDE") THEN
          sc.Scan; Init(item.include); 
          LOOP
            IF sc.type=tr.string THEN 
              IntStr.IntToStr(id, idstr); INC(id);
              item.include.AddItem(idstr, sc.string, err);
              sc.Scan;
              IF (sc.type=tr.char) & (sc.char=",") THEN sc.Scan
              ELSE EXIT 
              END
            ELSE Error(err, expectingString, file, sc.pos); EXIT
            END 
          END
        END;
        AddLocale(loc, item)
      END
    ELSE Error(err, expectingString, file, sc.pos)
    END
  END GetLocale;
  
  PROCEDURE GetLocales (fname: ARRAY OF CHAR; VAR loc: ptr);
  BEGIN
    (* open the catalog file *)
    f:=Files.Old(fname, {Files.read}, status);
    IF f=NIL THEN RETURN END;
    sc:=tr.ConnectScanner(f);
    IF sc=NIL THEN RETURN END;
    
    (* read the locales *)
    sc.Scan; ClearError(err);
    WHILE (err.err=noError) & (sc.type=tr.char) & (sc.char="#") DO Comment(fname, sc, err) END;   
    IF (sc.type=tr.ident) & (sc.string="PATH") THEN
      sc.Scan;
      IF sc.type=tr.string THEN 
        COPY(sc.string, path);
        sc.Scan
      ELSE Error(err, expectingString, fname, sc.pos)
      END
    END;
    REPEAT
      IF (sc.type=tr.ident) & (sc.string="LOCALE") THEN GetLocale(loc)
      ELSIF (sc.type=tr.char) & (sc.char="#") THEN Comment(fname, sc, err)
      ELSE Error(err, expectingLocaleCom, fname, sc.pos)
      END
    UNTIL (err.err#noError) OR (sc.type IN {tr.error, tr.invalid});
  END GetLocales;
  
BEGIN
  (* extract the base directory *)
  Filenames.GetPath(file, dir, name);
  Filenames.ExpandPath(dir, dir);
  
  (* read the locales *)
  NEW(loc); COPY("", path);
  total:=0; loc:=NIL; GetLocales(name, loc);
  IF (loc=NIL) OR (total=0) THEN 
    Error(err, masterNotFound, name, 0); RETURN
  END;
  
  (* transfer to an array *)
  NEW(locList); NEW(locList.loc, total);
  NEW(locList.dir, s.Length(dir)+1); COPY(dir, locList.dir^);
  NEW(locList.path, s.Length(path)+1); COPY(path, locList.path^);
  FOR cnt:=0 TO total-1 DO
    locList.loc[cnt]:=loc^;
    loc:=loc.next
  END
END ReadLocales;

PROCEDURE Test;
VAR 
  locales: Locales; 
  sec: Section; id: LONGINT;
  errstr: ARRAY 256 OF CHAR;
  err: ErrDesc;
  
  PROCEDURE Output;
  VAR i: INTEGER; str: ARRAY 64 OF CHAR;
  BEGIN
    IF err.err#noError THEN 
      ErrorDescr(err, errstr);
      Out.String("Error: "); Out.String(errstr); Out.Ln;      
      (* RETURN *)
    END;
    sec:=dbase.GetSection("LocText.months");     
    IF sec=dbase THEN RETURN END;
    Out.String("Obtained section: "); sec.GetSelector(str);
    Out.String(str); Out.Ln;
    Out.String("Locale items are..."); Out.Ln;
    Out.String("Months of the year:"); Out.Ln;
    FOR i:=0 TO 12 DO
      sec.GetElement("", i, str);
      IF ~IsError(str) THEN Out.Int(i, 1); Out.String(" = ");
        Out.String(str); Out.Ln
      END
    END;
    
    sec:=dbase.GetSection("LocText");     
    IF sec=dbase THEN RETURN END; 
    Out.String("Obtained section: "); sec.GetSelector(str);
    Out.String(str); Out.Ln;    
    Out.String("Days of the week:"); Out.Ln;
    FOR i:=0 TO 7 DO
      sec.GetElement("days", i, str);
      IF ~IsError(str) THEN Out.Int(i, 1); Out.String(" = ");
        Out.String(str); Out.Ln
      END
    END;
    
    sec.Get("embeddedSpaces", str);
    Out.String("Embedded spaces: "); Out.String(str); Out.Ln;
    
    sec:=dbase.GetSection("OOC.LocText");
    IF sec=dbase THEN RETURN END;
    Out.String("Obtained section: "); sec.GetSelector(str);
    Out.String(str); Out.Ln;    
    Out.String("Imported section:"); Out.Ln;    
    FOR i:=0 TO 20 DO
      sec.GetElement("", i, str);
      IF ~IsError(str) THEN Out.Int(i, 1); Out.String(" = ");
        Out.String(str); Out.Ln
      END    
    END
  END Output;
  
BEGIN
  (* output the available languages *)
  ReadLocales("loctest.mas", locales, err);
  IF err.err#noError THEN 
    Out.String("Error: "); ErrorDescr(err, errstr);
    Out.String(errstr); Out.Ln;
    RETURN
  END;  
  FOR id:=0 TO LEN(locales.loc^)-1 DO
    Out.Ln;
    Out.String("Locale "); Out.String(locales.loc[id].locale^);
    Out.String(" = "); Out.String(locales.loc[id].catalog^); Out.Ln;
    SetLocale(locales, locales.loc[id].locale^, err); 
    Output
  END
END Test;

BEGIN 
  NEW (errorContext);
  Msg.InitContext (errorContext, "OOC:Core:LocText");

  Init(dbase);               (* create an empty section head for dbase *)
  l.GetText:=ExpErrorDescr;  (* initialize error description routine *)
  IF DEBUG THEN Test END
END LocText.





