(*      $Id: Msg.Mod,v 1.10 2000/03/01 09:55:55 ooc-devel Exp $   *)
MODULE Msg [OOC_EXTENSIONS];
(*  Framework for messages (creation, expansion, conversion to text).
    Copyright (C) 1999, 2000  Michael van Acken

    This module is free software; you can redistribute it and/or
    modify it under the terms of the GNU Lesser General Public License
    as published by the Free Software Foundation; either version 2 of
    the License, or (at your option) any later version.

    This module is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
    Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public
    License along with OOC. If not, write to the Free Software Foundation,
    59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
*)


(*

This module combines several concepts: messages, message attributes,
message contexts, and message lists.  This four aspects make this
module a little bit involved, but at the core it is actually very
simple.

The topics attributes and contexts are primarily of interest for
modules that generate messages.  They determine the content of the
message, and how it can be translated into readable text.  A user will
mostly be in the position of message consumer, and will be handed
filled in message objects.  For a user, the typical operation will be
to convert a message into descriptive text (see methode GetText() and
GetLText()).

Message lists are a convenience feature for modules like parsers,
which normally do not abort after a single error message.  Usually,
they try to continue their work after an error, looking for more
problems and possibly emitting more error messages.

*)

IMPORT
  CharClass, Strings, LongStrings, IntStr;

CONST
  sizeAttrName* = 128-1;
  (* Maximum length of the attribute name for `InitAttribute', 
     `NewIntAttrib', `NewStringAttrib', `NewLStringAttrib', or 
     `NewMsgAttrib'.  *)
  sizeAttrReplacement* = 16*1024-1;
  (* Maximum length of an attribute's replacement text.  *)
  
TYPE  (* the basic string and character types used by this module: *)
  Char* = CHAR;
  String* = ARRAY OF Char;
  StringPtr* = POINTER TO String;
  
  LChar* = LONGCHAR;
  LString* = ARRAY OF LChar;
  LStringPtr* = POINTER TO LString;
  
  Code* = LONGINT;
  (* Identifier for a message's content.  Together with the message context,
     this value uniquely identifies the type of the message.  *)

TYPE
  Attribute* = POINTER TO AttributeDesc;
  AttributeDesc* = RECORD [ABSTRACT]
    (* An attribute is a (name, value) tuple, which can be associated with
       a message.  When a message is tranlated into its readable version 
       through the `GetText' function, the value part is first converted to
       some textual representation, and then inserted into the message's text.
       Within a message, an attribute is uniquely identified by its name.  *)
    nextAttrib-: Attribute;
    name-: StringPtr;             (* restricted to `sizeAttrName' characters *)
  END;

TYPE
  Context* = POINTER TO ContextDesc;
  ContextDesc* = RECORD
    (* Describes the context under which messages are converted into
       their textual representation.  Together, a message's context and
       its code identify the message type.  As a debugging aid, an 
       identification string can be associated with a context object (see
       procedure `InitContext').  *)
    id-: StringPtr;
  END;
  
TYPE
  Msg* = POINTER TO MsgDesc;
  MsgDesc* = RECORD
    (* A message is an object that can be converted to human readable text
       and presented to a program's user.  Within the OOC library, messages
       are used to store errors in the I/O modules, and the XML library uses
       them to create an error list when parsing an XML document.
       
       A message's type is uniquely identified by its context and its code.
       Using these two attributes, a message can be converted to text.  The
       text may contain placeholders, which are filled by the textual
       representation of attribute values associated with the message.  *)
    nextMsg-, prevMsg-: Msg;  (* initialized to NIL, used by `MsgList' *)
    code-: Code;
    context-: Context;
    attribList-: Attribute;       (* sorted by name *)
  END;

TYPE
  MsgList* = POINTER TO MsgListDesc;
  MsgListDesc* = RECORD
    msgCount-: LONGINT;                  (* number of messages *)
    msgList-, lastMsg: Msg;
  END;

TYPE (* default implementations for some commonly used message attributes: *)
  IntAttribute* = POINTER TO IntAttributeDesc;
  IntAttributeDesc = RECORD
    (AttributeDesc)
    int-: LONGINT;
  END;
  StringAttribute* = POINTER TO StringAttributeDesc;
  StringAttributeDesc = RECORD
    (AttributeDesc)
    string-: StringPtr;
  END;
  LStringAttribute* = POINTER TO LStringAttributeDesc;
  LStringAttributeDesc = RECORD
    (AttributeDesc)
    string-: LStringPtr;
  END;
  MsgAttribute* = POINTER TO MsgAttributeDesc;
  MsgAttributeDesc = RECORD
    (AttributeDesc)
    msg-: Msg;
  END;


(* Context
   ------------------------------------------------------------------------ *)

PROCEDURE InitContext* (context: Context; id: String);
(* The string argument `id' should describe the message context to the
   programmer.  It should not appear in output generated for a
   program's user, or at least it should not be necessary for a user
   to interpret ths string to understand the message.  It is a good
   idea to use the module name of the context variable for the
   identifier.  If this is not sufficient to identify the variable,
   add the variable name to the string.  *)
  BEGIN
    NEW (context. id, Strings.Length (id)+1);
    COPY (id, context. id^)
  END InitContext;

PROCEDURE (context: Context) GetTemplate* (msg: Msg; VAR templ: LString);
(* Returns a template string for the message `msg'.  The string may
   contain attribute references.  Instead of the reference `${foo}',
   the procedure `GetText' (see below) will insert the textual
   representation of the attribute with the name `foo'.  The special
   reference `${MSG_CONTEXT}' is replaced by the value of
   `context.id', and `${MSG_CODE}' with `msg.code'.
   
   The default implementation returns this string:
     MSG_CONTEXT: ${MSG_CONTEXT}
     MSG_CODE: ${MSG_CODE}
     attribute_name: ${attribute_name}
   
   The last list is repeated for every attribute name.  The lines are
   separated by `CharClass.eol'.  
   
   pre: msg # NIL *)
  VAR
    attrib: Attribute;
    buffer: ARRAY sizeAttrReplacement+1 OF LONGCHAR;
  BEGIN
    (* default implementation: the template contains the context identifier,
       the error number, and the full list of attributes *)
    COPY ("MSG_CONTEXT: ${MSG_CONTEXT}", templ);
    LongStrings.Append (CharClass.eol, templ);
    LongStrings.Append ("MSG_CODE: ${MSG_CODE}", templ);
    LongStrings.Append (CharClass.eol, templ);
    attrib := msg. attribList;
    WHILE (attrib # NIL) DO
      COPY (attrib. name^, buffer);      (* extend to LONGCHAR *)
      LongStrings.Append (buffer, templ);
      LongStrings.Append (": ${", templ);
      LongStrings.Append (buffer, templ);
      LongStrings.Append ("}", templ);
      LongStrings.Append (CharClass.eol, templ);
      attrib := attrib. nextAttrib
    END
  END GetTemplate;


(* Attribute Functions
   ------------------------------------------------------------------------ *)

PROCEDURE InitAttribute* (attr: Attribute; name: String);
(* Initializes attribute object and sets its name.  *)
  BEGIN
    attr. nextAttrib := NIL;
    NEW (attr. name, Strings.Length (name)+1);
    COPY (name, attr. name^)
  END InitAttribute;

PROCEDURE (attr: Attribute) [ABSTRACT] ReplacementText* (VAR text: LString);
(* Converts attribute value into some textual representation.  The length of
   the resulting string must not exceed `sizeAttrReplacement' characters:
   `GetLText()' calls this procedure with a text buffer of
   `sizeAttrReplacement+1' bytes.  *)
  END ReplacementText;


(* Message Functions
   ------------------------------------------------------------------------ *)

PROCEDURE New* (context: Context; code: Code): Msg;
(* Creates a new message object for the given context, using the specified
   message code.  The message's attribute list is empty.  *)
  VAR
    msg: Msg;
  BEGIN
    NEW (msg);
    msg. prevMsg := NIL;
    msg. nextMsg := NIL;
    msg. code := code;
    msg. context := context;
    msg. attribList := NIL;
    RETURN msg
  END New;

PROCEDURE (msg: Msg) SetAttribute* (attr: Attribute);
(* Append an attribute to the message's attribute list.  If an attribute of
   the same name exists already, it is replaced by the new one.
   pre: Length(attr.name^)<=sizeAttrName
        `attr' has not been attached to any other message *)
  
  PROCEDURE Insert (VAR aList: Attribute; attr: Attribute);
    BEGIN
      IF (aList = NIL) THEN                (* append to list *)
        aList := attr
      ELSIF (aList. name^ = attr. name^) THEN (* replace element aList *)
        attr. nextAttrib := aList. nextAttrib;
        aList := attr
      ELSIF (aList. name^ > attr.name^) THEN (* insert element before aList *)
        attr. nextAttrib := aList;
        aList := attr
      ELSE                                 (* continue with next element *)
        Insert (aList. nextAttrib, attr)
      END
    END Insert;

  BEGIN
    Insert (msg. attribList, attr)
  END SetAttribute;

PROCEDURE (msg: Msg) GetAttribute* (name: String): Attribute;
(* Returns the attribute `name' of the message object.  If no such attribute
   exists, the value NIL is returned.  *)
  VAR
    a: Attribute;
  BEGIN
    a := msg. attribList;
    WHILE (a # NIL) & (a. name^ # name) DO
      a := a. nextAttrib
    END;
    RETURN a
  END GetAttribute;

PROCEDURE (msg: Msg) GetLText* (VAR text: LString);
(* Converts a message into a string.  The basic format of the string is 
   determined by calling `msg.context.GetTemplate'.  Then the attributes
   are inserted into the template string: the placeholder string `${foo}' 
   is replaced with the textual representation of attribute.
   
   pre: LEN(text)<2^15
   Note: Behaviour is undefined if replacement text of attribute contains an
         attribute reference.  *)
  VAR
    attr: Attribute;
    attrName: ARRAY sizeAttrName+4 OF LONGCHAR;
    insert: ARRAY sizeAttrReplacement+1 OF LONGCHAR;
    found: BOOLEAN;
    pos, len: INTEGER;
    num: ARRAY 48 OF CHAR;
  BEGIN
    msg. context. GetTemplate (msg, text);
    attr := msg. attribList;
    WHILE (attr # NIL) DO
      COPY (attr. name^, attrName);
      LongStrings.Insert ("${", 0, attrName);
      LongStrings.Append ("}", attrName);
      
      LongStrings.FindNext (attrName, text, 0, found, pos);
      WHILE found DO
        len := LongStrings.Length (attrName);
        LongStrings.Delete (text, pos, len);
        attr. ReplacementText (insert);
        LongStrings.Insert (insert, pos, text);
        LongStrings.FindNext (attrName, text, pos+LongStrings.Length (insert),
                              found, pos)
      END;
      
      attr := attr. nextAttrib
    END;
    
    LongStrings.FindNext ("${MSG_CONTEXT}", text, 0, found, pos);
    IF found THEN
      LongStrings.Delete (text, pos, 14);
      COPY (msg. context. id^, insert);
      LongStrings.Insert (insert, pos, text)
    END;
    
    LongStrings.FindNext ("${MSG_CODE}", text, 0, found, pos);
    IF found THEN
      LongStrings.Delete (text, pos, 11);
      IntStr.IntToStr (msg. code, num);
      COPY (num, insert);
      LongStrings.Insert (insert, pos, text)
    END    
  END GetLText;

PROCEDURE (msg: Msg) GetText* (VAR text: String);
(* Like `GetLText', but the message text is truncated to ISO-Latin1 
   characters.  All characters that are not part of ISO-Latin1 are mapped
   to question marks "?".  *)
  VAR
    buffer: ARRAY ASH(2,15)-1 OF LChar;
    i: INTEGER;
  BEGIN
    msg. GetLText (buffer);
    i := -1;
    REPEAT
      INC (i);
      IF (buffer[i] <= 0FFX) THEN
        text[i] := SHORT (buffer[i])
      ELSE
        text[i] := "?"
      END
    UNTIL (text[i] = 0X)
  END GetText;


(* Message List
   ------------------------------------------------------------------------ *)
   
PROCEDURE InitMsgList* (l: MsgList);
  BEGIN
    l. msgCount := 0;
    l. msgList := NIL;
    l. lastMsg := NIL
  END InitMsgList;

PROCEDURE NewMsgList* (): MsgList;
  VAR
    l: MsgList;
  BEGIN
    NEW (l);
    InitMsgList (l);
    RETURN l
  END NewMsgList;

PROCEDURE (l: MsgList) Append* (msg: Msg);
(**Appends the message `msg'.  to the list `l'.

   pre: `msg' is not part of another message list.  *)
  BEGIN
    msg. nextMsg := NIL;
    IF (l. msgList = NIL) THEN
      msg. prevMsg := NIL;
      l. msgList := msg
    ELSE
      msg. prevMsg := l. lastMsg;
      l. lastMsg. nextMsg := msg
    END;
    l. lastMsg := msg;
    INC (l. msgCount)
  END Append;

PROCEDURE (l: MsgList) AppendList* (source: MsgList);
(**Appends the messages of list `source' to `l'.  Afterwards, `source' is
   an empty list, and the elements of `source' can be found at the end of
   the list `l'.  *)
  BEGIN
    IF (source. msgCount # 0) THEN
      IF (l. msgCount = 0) THEN
        l^ := source^
      ELSE  (* both `source' and `l' are not empty *)
        INC (l. msgCount, source. msgCount);
        l. lastMsg. nextMsg := source. msgList;
        source. msgList. prevMsg := l. lastMsg;
        l. lastMsg := source. lastMsg;
        InitMsgList (source)
      END
    END
  END AppendList;


(* Standard Attributes
   ------------------------------------------------------------------------ *)
   
PROCEDURE NewIntAttrib* (name: String; value: LONGINT): IntAttribute;
(* pre: Length(name)<=sizeAttrName *)
  VAR
    attr: IntAttribute;
  BEGIN
    NEW (attr);
    InitAttribute (attr, name);
    attr. int := value;
    RETURN attr
  END NewIntAttrib;

PROCEDURE (msg: Msg) SetIntAttrib* (name: String; value: LONGINT);
(* pre: Length(name)<=sizeAttrName *)
  BEGIN
    msg. SetAttribute (NewIntAttrib (name, value))
  END SetIntAttrib;

PROCEDURE (attr: IntAttribute) ReplacementText* (VAR text: LString);
  VAR
    num: ARRAY 48 OF CHAR;
  BEGIN
    IntStr.IntToStr (attr. int, num);
    COPY (num, text)
  END ReplacementText;

PROCEDURE NewStringAttrib* (name: String; value: StringPtr): StringAttribute;
(* pre: Length(name)<=sizeAttrName *)
  VAR
    attr: StringAttribute;
  BEGIN
    NEW (attr);
    InitAttribute (attr, name);
    attr. string := value;
    RETURN attr
  END NewStringAttrib;

PROCEDURE (msg: Msg) SetStringAttrib* (name: String; value: StringPtr);
(* pre: Length(name)<=sizeAttrName *)
  BEGIN
    msg. SetAttribute (NewStringAttrib (name, value))
  END SetStringAttrib;

PROCEDURE (attr: StringAttribute) ReplacementText* (VAR text: LString);
  BEGIN
    COPY (attr. string^, text)
  END ReplacementText;

PROCEDURE NewLStringAttrib* (name: String; value: LStringPtr): LStringAttribute;
(* pre: Length(name)<=sizeAttrName *)
  VAR
    attr: LStringAttribute;
  BEGIN
    NEW (attr);
    InitAttribute (attr, name);
    attr. string := value;
    RETURN attr
  END NewLStringAttrib;

PROCEDURE (msg: Msg) SetLStringAttrib* (name: String; value: LStringPtr);
(* pre: Length(name)<=sizeAttrName *)
  BEGIN
    msg. SetAttribute (NewLStringAttrib (name, value))
  END SetLStringAttrib;

PROCEDURE (attr: LStringAttribute) ReplacementText* (VAR text: LString);
  BEGIN
    COPY (attr. string^, text)
  END ReplacementText;

PROCEDURE NewMsgAttrib* (name: String; value: Msg): MsgAttribute;
(* pre: Length(name)<=sizeAttrName *)
  VAR
    attr: MsgAttribute;
  BEGIN
    NEW (attr);
    InitAttribute (attr, name);
    attr. msg := value;
    RETURN attr
  END NewMsgAttrib;

PROCEDURE (msg: Msg) SetMsgAttrib* (name: String; value: Msg);
(* pre: Length(name)<=sizeAttrName *)
  BEGIN
    msg. SetAttribute (NewMsgAttrib (name, value))
  END SetMsgAttrib;

PROCEDURE (attr: MsgAttribute) ReplacementText* (VAR text: LString);
  BEGIN
    attr. msg. GetLText (text)
  END ReplacementText;



(* Auxiliary functions
   ------------------------------------------------------------------------ *)

PROCEDURE GetStringPtr* (str: String): StringPtr;
(* Creates a copy of `str' on the heap and returns a pointer to it.  *)
  VAR
    s: StringPtr;
  BEGIN
    NEW (s, Strings.Length (str)+1);
    COPY (str, s^);
    RETURN s
  END GetStringPtr;

PROCEDURE GetLStringPtr* (str: LString): LStringPtr;
(* Creates a copy of `str' on the heap and returns a pointer to it.  *)
  VAR
    s: LStringPtr;
  BEGIN
    NEW (s, LongStrings.Length (str)+1);
    COPY (str, s^);
    RETURN s
  END GetLStringPtr;

END Msg.
