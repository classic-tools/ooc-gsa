(* 	$Id: Worklist.Mod,v 1.11 1996/09/26 08:09:05 jnzimmer Exp $	 *)
MODULE Worklist;
(*  ...
    Copyright (C) 1995  Juergen Zimmermann

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
  O := Out, D := Data;

CONST
  ownGC = TRUE;

TYPE
  Node* = POINTER TO NodeDesc;
  
  UsingHook* = PROCEDURE (used: D.Result; instr: D.Instruction): BOOLEAN;  
  (* this is the function called when `Worklist.AddUsingInstr' is used *)

  InitHook* = PROCEDURE (instr: D.Instruction): BOOLEAN;
  
  
  WorklistPtr* = POINTER TO Worklist;
  Worklist* = RECORD
    (D.InfoDesc)
    head, tail: Node;
  END;
  
  NodeDesc* = RECORD
    nextNode-, prevNode-: Node;
    data-: D.Info
  END;

VAR
  garbage: Node;

PROCEDURE (VAR wl: Worklist) Init*;
  BEGIN
    wl. head := NIL;
    wl. tail := NIL
  END Init;

PROCEDURE NewNode (data: D.Info): Node;
  VAR
    newNode: Node;
  BEGIN
    IF ownGC & (garbage # NIL) THEN
      newNode := garbage;
      garbage := garbage. nextNode;
    ELSE
      NEW (newNode);
    END;
    newNode. data := data;
    newNode. nextNode := NIL;
    newNode. prevNode := NIL;
    RETURN newNode
  END NewNode;

PROCEDURE DisposeNode* (VAR node: Node);
  BEGIN
    IF ownGC THEN
      node. nextNode := garbage;
      node. prevNode := NIL;
      node. data := NIL;
      garbage := node;
    END;
    node := NIL;
  END DisposeNode;

PROCEDURE (node: Node) ReplaceData* (data: D.Info);
  BEGIN
    node. data := data;    
  END ReplaceData;


PROCEDURE (VAR wl: Worklist) GetNode* (data: D.Info): Node;
  VAR
    walk: Node;
  BEGIN
    walk := wl. head;
    WHILE (walk # NIL) & (data # walk. data) DO
      walk := walk. nextNode;
    END;
    RETURN walk;
  END GetNode;

PROCEDURE (VAR wl: Worklist) Member* (data: D.Info): BOOLEAN;
  BEGIN
    RETURN (wl.GetNode (data) # NIL);
  END Member;

PROCEDURE (VAR wl: Worklist) MemberNode* (node: Node): BOOLEAN;
  VAR
    walk: Node;
  BEGIN
    walk := wl. head;
    WHILE (walk # NIL) & (walk # node) DO
      walk := walk. nextNode;
    END;
    RETURN (walk # NIL);
  END MemberNode;

  
PROCEDURE (VAR wl: Worklist) RemoveNode* (node: Node);
(* pre: `node' is member of `wl'
   post: `node' is no longer member of `wl' *)
  VAR
    prev, next: Node;
  BEGIN
    IF ~wl.MemberNode (node) THEN
      O.String ("RemoveNode: node not in list"); O.Ln; HALT (100);
    ELSE
      prev := node. prevNode;
      next := node. nextNode;
      node. nextNode := NIL;
      node. prevNode := NIL;
  
      IF (prev = NIL) THEN
        wl. head := next;
      ELSE
        prev. nextNode := next;
      END;
      
      IF (next = NIL) THEN
        wl. tail := prev;
      ELSE
        next. prevNode := prev;
      END;
    END;
  END RemoveNode;


PROCEDURE (VAR wl: Worklist) AddNodeHead* (node: Node);
  BEGIN
    IF (wl. head = NIL) THEN
      wl. tail := node;
    ELSE
      wl. head. prevNode := node;
    END;
    node. nextNode := wl. head;
    node. prevNode := NIL;
    wl. head := node;
  END AddNodeHead;

PROCEDURE (VAR wl: Worklist) AddHead* (data: D.Info);
  VAR
    newNode: Node;
  BEGIN
    newNode := NewNode (data);
    wl.AddNodeHead (newNode);
  END AddHead;

PROCEDURE (VAR wl: Worklist) AddHeadUnique* (data: D.Info);
  VAR
    node: Node;
  BEGIN
    node := wl.GetNode (data);
    IF (node # NIL) THEN
      wl.RemoveNode (node);
      wl.AddNodeHead (node);
    ELSE
      wl.AddHead (data);
    END;
  END AddHeadUnique;


PROCEDURE (VAR wl: Worklist) AddNodeTail* (node: Node);
  BEGIN
    IF (wl. tail = NIL) THEN
      wl. head := node;
    ELSE
      wl. tail. nextNode := node;
    END;
    node. prevNode := wl. tail;
    node. nextNode := NIL;
    wl. tail := node;
  END AddNodeTail;

PROCEDURE (VAR wl: Worklist) AddTail* (data: D.Info);
  VAR
    newNode: Node;
  BEGIN
    newNode := NewNode (data);
    wl.AddNodeTail (newNode);
  END AddTail;

PROCEDURE (VAR wl: Worklist) AddTailUnique* (data: D.Info);
  VAR
    node: Node;
  BEGIN
    node := wl.GetNode (data);
    IF (node # NIL) THEN
      wl.RemoveNode (node);
      wl.AddNodeTail (node);
    ELSE
      wl.AddTail (data);
    END;
  END AddTailUnique;


PROCEDURE (VAR wl: Worklist) MoveNodeHead* (node: Node);
(* PRE: wl.MemberNode (node) == TRUE *)
  BEGIN
    wl.RemoveNode (node);
    wl.AddNodeHead (node);
  END MoveNodeHead;

PROCEDURE (VAR wl: Worklist) MoveNodeTail* (node: Node);
(* PRE: wl.MemberNode (node) == TRUE *)
  BEGIN
    wl.RemoveNode (node);
    wl.AddNodeTail (node);
  END MoveNodeTail;


PROCEDURE (VAR wl: Worklist) IsEmpty* (): BOOLEAN;
  BEGIN
    RETURN (wl. head = NIL);
  END IsEmpty;


PROCEDURE (VAR wl: Worklist) GetHeadNode* (): Node;
  BEGIN
    IF ~wl.IsEmpty () THEN
      RETURN wl. head;
    ELSE
      RETURN NIL;
    END;
  END GetHeadNode;

PROCEDURE (VAR wl: Worklist) GetHead* (): D.Info;
  BEGIN
    IF ~wl.IsEmpty () THEN
      RETURN wl. head. data;
    ELSE
      RETURN NIL;
    END
  END GetHead;

PROCEDURE (VAR wl: Worklist) GetTailNode* (): Node;
  BEGIN
    IF ~wl.IsEmpty () THEN
      RETURN wl. tail;
    ELSE
      RETURN NIL;
    END  
  END GetTailNode;

PROCEDURE (VAR wl: Worklist) GetTail* (): D.Info;
  BEGIN
    IF ~wl.IsEmpty () THEN
      RETURN wl. tail. data;
    ELSE
      RETURN NIL;
    END  
  END GetTail;

PROCEDURE (VAR wl: Worklist) RemoveHead*;
  VAR
    node: Node;
  BEGIN
    IF ~wl.IsEmpty() THEN
      node := wl. head;
      wl.RemoveNode (node);
      DisposeNode (node); 
    END;
  END RemoveHead;

PROCEDURE (VAR wl: Worklist) RemoveTail*;
  VAR
    node: Node;
  BEGIN
    IF ~wl.IsEmpty() THEN
      node := wl. tail;
      wl.RemoveNode (node);
      DisposeNode (node);
    END;   
  END RemoveTail;


PROCEDURE (VAR wl: Worklist) Clear*;
  BEGIN
    WHILE ~wl.IsEmpty() DO
      wl.RemoveHead;
    END;
  END Clear;
  
PROCEDURE (VAR wl: Worklist) Length* (): LONGINT;
  VAR
    num: LONGINT;
    node: Node;
  BEGIN
    num := 0;
    node := wl. head;
    WHILE (node # NIL) DO
      INC (num);
      node := node. nextNode;
    END;
    RETURN num;
  END Length;

PROCEDURE (VAR wl: Worklist) AddInstr* (region: D.Region; hook: InitHook);
  VAR
    instr: D.Instruction;
  BEGIN
    instr := region. instrList;
    WHILE (instr # NIL) DO
      IF (hook = NIL) OR hook (instr) THEN
        wl. AddTail (instr);
      END;
      instr := instr. nextInstr;
    END;
  END AddInstr;

PROCEDURE (VAR wl: Worklist) AddInstrUnique* (region: D.Region; hook: InitHook);
  VAR
    instr: D.Instruction;
  BEGIN
    instr := region. instrList;
    WHILE (instr # NIL) DO
      IF (hook = NIL) OR hook (instr) THEN
        wl. AddTailUnique (instr);
      END;
      instr := instr. nextInstr;
    END;
  END AddInstrUnique;

PROCEDURE (VAR wl: Worklist) AddUsingInstr* (used: D.Result; hook: UsingHook);
  VAR
    use: D.Opnd;
    instr: D.Instruction;
  BEGIN
    use := used. useList;
    WHILE (use # NIL) DO
      instr := use. instr;
      IF (hook = NIL) OR hook (used, instr) THEN
        wl.AddTail (instr);
      END;
      use := use. nextUse;
    END;
  END AddUsingInstr;

PROCEDURE (VAR wl: Worklist) AddUsingInstrUnique* (used: D.Result; hook: UsingHook);
  VAR
    use: D.Opnd;
    instr: D.Instruction;
  BEGIN
    use := used. useList;
    WHILE (use # NIL) DO
      instr := use. instr;
      IF (hook = NIL) OR hook (used, instr) THEN
        wl.AddTailUnique (instr);
      END;
      use := use. nextUse;
    END;
  END AddUsingInstrUnique;

BEGIN
  garbage := NIL;
END Worklist.
