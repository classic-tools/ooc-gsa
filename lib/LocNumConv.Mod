(*	$Id: LocNumConv.Mod,v 1.3 1999/09/02 13:10:07 acken Exp $	*)
MODULE LocNumConv;
 
 (*
    LocNumConv -  Localized number conversions.       
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
 
IMPORT
  Char:=CharClass, RC:=LRealConv, Str:=Strings, Conv:=ConvTypes, Locales;
 
TYPE
  ConvResults*= Conv.ConvResults; (* strAllRight, strOutOfRange, strWrongFormat, strEmpty *)

CONST
  strAllRight*=Conv.strAllRight;       (* the string format is correct for the corresponding conversion *)
  strOutOfRange*=Conv.strOutOfRange;   (* the string is well-formed but the value cannot be represented *)
  strWrongFormat*=Conv.strWrongFormat; (* the string is in the wrong format for the conversion *)
  strEmpty*=Conv.strEmpty;             (* the given string is empty *)

VAR
  RS, P, F, SR, RS2, P2, N2, F2, G2, SR2: Conv.ScanState;
  dpStr, sepStr, intCur, locCur, nSign, pSign: ARRAY 8 OF CHAR;
  ppos, npos: LONGINT;
  
PROCEDURE Localize;
VAR
  ok: BOOLEAN;
BEGIN
  (* localization parameters *)
  ok:=Locales.GetStr(Locales.decimalPoint, dpStr);
  ok:=Locales.GetStr(Locales.thousandsSep, sepStr);
  nSign:="-"; pSign:="+";
END Localize;

PROCEDURE LocalizeMoney;
VAR
  ok: BOOLEAN;
BEGIN
  (* localization parameters *)
  ok:=Locales.GetStr(Locales.monDecimalPoint, dpStr);
  ok:=Locales.GetStr(Locales.monThousandsSep, sepStr);
  ok:=Locales.GetStr(Locales.intCurrencySymbol, intCur);
  ok:=Locales.GetStr(Locales.currencySymbol, locCur);
  ok:=Locales.GetStr(Locales.negativeSign, nSign);
  ok:=Locales.GetStr(Locales.positiveSign, pSign);
  ppos:=Locales.GetInt(Locales.pSignPosn);
  npos:=Locales.GetInt(Locales.nSignPosn)
END LocalizeMoney;
  
PROCEDURE IsSign (ch: CHAR): BOOLEAN;
(* Return TRUE for '+' or '-' *)
BEGIN
  RETURN (nSign[0]#0X) & (ch=nSign[0]) OR
         (pSign[0]#0X) & (ch=pSign[0])
END IsSign; 

PROCEDURE IsDP (ch: CHAR): BOOLEAN;
(* Return TRUE for localization decimal point. *)
BEGIN
  RETURN (dpStr[0]#0X) & (ch=dpStr[0])
END IsDP;

PROCEDURE IsSeparator (ch: CHAR): BOOLEAN;
(* Return TRUE for localization separator. *)
BEGIN
  RETURN (sepStr[0]#0X) & (ch=sepStr[0])
END IsSeparator;

PROCEDURE Pos (find, str: ARRAY OF CHAR) : BOOLEAN;
VAR
  found: BOOLEAN;
  where: INTEGER;
BEGIN
  Str.FindNext(find, str, 0, found, where);
  RETURN found
END Pos;

PROCEDURE IsPrefix (ch: CHAR): BOOLEAN;
(* Return TRUE for localization prefix. *)
VAR
  find: ARRAY 2 OF CHAR;
BEGIN
  find[0]:=ch; find[1]:=0X;
  RETURN Pos(find, intCur) OR Pos(find, locCur) OR
         (ppos=0) & (ch='(') OR (npos=0) & (ch='(') OR
         (ch=' ')
END IsPrefix;

PROCEDURE IsSuffix (ch: CHAR): BOOLEAN;
(* Return TRUE for localization prefix. *)
VAR
  find: ARRAY 2 OF CHAR;
BEGIN
  find[0]:=ch; find[1]:=0X;
  RETURN Pos(find, intCur) OR Pos(find, locCur) OR
         (ppos=0) & (ch=')') OR (npos=0) & (ch=')') OR
         (ch=' ')
END IsSuffix;

(* internal state machine procedures *)

PROCEDURE RSState(inputCh: CHAR; VAR chClass: Conv.ScanClass; VAR nextState: Conv.ScanState);
BEGIN
  IF Char.IsNumeric(inputCh) THEN chClass:=Conv.valid; nextState:=P
  ELSE chClass:=Conv.invalid; nextState:=RS
  END
END RSState;
  
PROCEDURE PState(inputCh: CHAR; VAR chClass: Conv.ScanClass; VAR nextState: Conv.ScanState);
BEGIN
  IF Char.IsNumeric(inputCh) OR IsSeparator(inputCh) THEN chClass:=Conv.valid; nextState:=P
  ELSIF IsDP(inputCh) THEN chClass:=Conv.valid; nextState:=F 
  ELSIF IsSeparator(inputCh) THEN chClass:=Conv.padding; nextState:=P
  ELSE chClass:=Conv.terminator; nextState:=NIL
  END
END PState;
  
PROCEDURE FState(inputCh: CHAR; VAR chClass: Conv.ScanClass; VAR nextState: Conv.ScanState);
BEGIN
  IF Char.IsNumeric(inputCh) THEN chClass:=Conv.valid; nextState:=F  
  ELSE chClass:=Conv.terminator; nextState:=NIL
  END
END FState;
 
PROCEDURE ScanNumber*(inputCh: CHAR; VAR chClass: Conv.ScanClass; VAR nextState: Conv.ScanState);
 (* 
    Represents the start state of a finite state scanner for localized numbers - assigns
    class of inputCh to chClass and a procedure representing the next state to
    nextState.
    
    The call of ScanNumber(inputCh,chClass,nextState) shall assign values to
    `chClass' and `nextState' depending upon the value of `inputCh' as
    shown in the following table.
    
    Procedure       inputCh         chClass         nextState (a procedure
                                                    with behaviour of)
    ---------       ---------       --------        ---------
    ScanNumber      space           padding         ScanNumber
                    sign            valid           RSState
                    decimal digit   valid           PState
                    other           invalid         ScanNumber
    RSState         decimal digit   valid           PState
                    other           invalid         RSState
    PState          decimal digit   valid           PState
                    decimal point   valid           FState
                    separator       padding         PState
                    other           terminator      --
    FState          decimal digit   valid           FState
                    other           terminator      --
   
    For examples of how to use ScanNumber, refer to FormatNumber and
    ValueNumber below.     
  *)
BEGIN
  Localize;  (* set up localization parameters *)
  IF Char.IsWhiteSpace(inputCh) THEN chClass:=Conv.padding; nextState:=SR
  ELSIF IsSign(inputCh) THEN chClass:=Conv.valid; nextState:=RS
  ELSIF Char.IsNumeric(inputCh) THEN chClass:=Conv.valid; nextState:=P
  ELSE chClass:=Conv.invalid; nextState:=SR
  END
END ScanNumber;
 
PROCEDURE ValueNumberRes(str: ARRAY OF CHAR; VAR rn: LONGREAL; VAR res: ConvResults);
  (* 
     Returns the value corresponding to the number string value str 
     if str is well-formed; otherwise returns an error in res.
  *)
VAR
  ch: CHAR;
  state: Conv.ScanState;
  prev, class: Conv.ScanClass;
  index, pos, len: INTEGER;
  numb: ARRAY 64 OF CHAR;  
BEGIN
  state:=SR;
  len:=Str.Length(str); index:=0; pos:=0;  
  LOOP
    IF index=len THEN EXIT END;
    ch:=str[index];
    state.p(ch, class, state);
    CASE class OF
    | Conv.padding: (* nothing to do *)
    | Conv.valid:
        IF IsDP(ch) THEN numb[pos]:='.'; INC(pos) 
        ELSE numb[pos]:=ch; INC(pos) (* must be a digit *)
        END
    | Conv.invalid, Conv.terminator: EXIT
    END;
    prev:=class; INC(index)
  END;
  IF class IN {Conv.invalid, Conv.terminator} THEN 
    res:=strWrongFormat; rn:=0
  ELSIF prev=Conv.padding THEN 
    res:=strEmpty; rn:=0
  ELSE
    numb[pos]:=0X;
    res:=RC.FormatReal(numb);
    rn:=RC.ValueReal(numb)
  END  
END ValueNumberRes;

PROCEDURE FormatNumber*(str: ARRAY OF CHAR): ConvResults;
  (* Returns the format of the string value for conversion to number. *)
VAR res: ConvResults; x: LONGREAL;
BEGIN
  ValueNumberRes(str, x, res);
  RETURN res
END FormatNumber;
 
PROCEDURE ValueNumber*(str: ARRAY OF CHAR): LONGREAL;
VAR res: ConvResults; x: LONGREAL;
BEGIN
  ValueNumberRes(str, x, res);
  RETURN x
END ValueNumber;

PROCEDURE RS2State(inputCh: CHAR; VAR chClass: Conv.ScanClass; VAR nextState: Conv.ScanState);
BEGIN
  IF Char.IsNumeric(inputCh) THEN chClass:=Conv.valid; nextState:=P2
  ELSIF IsPrefix(inputCh) THEN chClass:=Conv.padding; nextState:=RS2
  ELSE chClass:=Conv.invalid; nextState:=RS2
  END
END RS2State;
  
PROCEDURE P2State(inputCh: CHAR; VAR chClass: Conv.ScanClass; VAR nextState: Conv.ScanState);
BEGIN
  IF Char.IsNumeric(inputCh) OR IsSeparator(inputCh) THEN chClass:=Conv.valid; nextState:=P2
  ELSIF IsDP(inputCh) THEN chClass:=Conv.valid; nextState:=F2
  ELSIF IsSeparator(inputCh) THEN chClass:=Conv.padding; nextState:=P2
  ELSE chClass:=Conv.terminator; nextState:=NIL
  END
END P2State;

PROCEDURE N2State(inputCh: CHAR; VAR chClass: Conv.ScanClass; VAR nextState: Conv.ScanState);
BEGIN
  IF Char.IsNumeric(inputCh) OR IsSeparator(inputCh) THEN chClass:=Conv.valid; nextState:=N2
  ELSIF IsDP(inputCh) THEN chClass:=Conv.valid; nextState:=G2
  ELSIF IsSeparator(inputCh) THEN chClass:=Conv.padding; nextState:=N2
  ELSE chClass:=Conv.terminator; nextState:=NIL
  END
END N2State;
  
PROCEDURE F2State(inputCh: CHAR; VAR chClass: Conv.ScanClass; VAR nextState: Conv.ScanState);
BEGIN
  IF Char.IsNumeric(inputCh) THEN chClass:=Conv.valid; nextState:=F2
  ELSIF IsSuffix(inputCh) THEN chClass:=Conv.padding; nextState:=F2
  ELSE chClass:=Conv.terminator; nextState:=NIL
  END
END F2State;

PROCEDURE G2State(inputCh: CHAR; VAR chClass: Conv.ScanClass; VAR nextState: Conv.ScanState);
BEGIN
  IF Char.IsNumeric(inputCh) THEN chClass:=Conv.valid; nextState:=G2
  ELSIF IsSuffix(inputCh) THEN chClass:=Conv.padding; nextState:=G2
  ELSIF IsSign(inputCh) THEN chClass:=Conv.valid; nextState:=G2
  ELSE chClass:=Conv.terminator; nextState:=NIL
  END
END G2State;

PROCEDURE ScanMoney*(inputCh: CHAR; VAR chClass: Conv.ScanClass; VAR nextState: Conv.ScanState);
 (* 
    Represents the start state of a finite state scanner for localized money - assigns
    class of inputCh to chClass and a procedure representing the next state to
    nextState.
    
    The call of ScanMoney(inputCh,chClass,nextState) shall assign values to
    `chClass' and `nextState' depending upon the value of `inputCh' as
    shown in the following table.
    
    Procedure       inputCh         chClass         nextState (a procedure
                                                    with behaviour of)
    ---------       ---------       --------        ---------
    ScanMoney       prefix          padding         ScanMoney
                    sign            valid           RS2State
                    decimal digit   valid           N2State
                    other           invalid         ScanMoney                   
    RS2State        decimal digit   valid           P2State
                    prefix          padding         RS2State
                    other           invalid         RS2State
    P2State         decimal digit   valid           P2State
                    decimal point   valid           F2State
                    separator       valid           P2State
                    other           terminator      --
    N2State         decimal digit   valid           N2State
                    decimal point   valid           G2State
                    separator       valid           N2State
                    other           terminator      --
    F2State         decimal digit   valid           F2State
                    suffix          padding         F2State
                    other           terminator      --
    G2State         decimal digit   valid           G2State
                    suffix          padding         G2State
                    sign            valid           
                    other           terminator      --
   
    For examples of how to use ScanMoney, refer to FormatMoney and
    ValueMoney below.     
  *)
BEGIN
  LocalizeMoney;  (* set up localization parameters *)
  IF IsPrefix(inputCh) THEN chClass:=Conv.padding; nextState:=SR2
  ELSIF IsSign(inputCh) THEN chClass:=Conv.valid; nextState:=RS2
  ELSIF Char.IsNumeric(inputCh) THEN chClass:=Conv.valid; nextState:=N2
  ELSE chClass:=Conv.invalid; nextState:=SR2
  END
END ScanMoney;
 
PROCEDURE ValueMoneyRes(str: ARRAY OF CHAR; VAR rn: LONGREAL; VAR res: ConvResults);
  (* 
     Returns the value corresponding to the money string value str 
     if str is well-formed; otherwise returns an error in res.
  *)
VAR
  ch: CHAR;
  state: Conv.ScanState;
  prev, class: Conv.ScanClass;
  index, pos, len: INTEGER;
  numb: ARRAY 64 OF CHAR;
  sign: ARRAY 2 OF CHAR;
BEGIN
  state:=SR2; 
  class:=Conv.padding; prev:=class;
  sign[0]:=0X; sign[1]:=0X;
  len:=Str.Length(str); index:=0; pos:=0;  
  LOOP
    IF index=len THEN EXIT END;
    ch:=str[index];
    state.p(ch, class, state);
    CASE class OF
    | Conv.padding:
        IF ch='(' THEN sign[0]:='-' END
    | Conv.valid:
        IF IsDP(ch) THEN numb[pos]:='.'; INC(pos)
        ELSIF IsSign(ch) THEN sign[0]:=ch
        ELSE numb[pos]:=ch; INC(pos) (* must be a digit *)
        END
    | Conv.invalid, Conv.terminator: EXIT
    END;
    prev:=class; INC(index)
  END;
  IF class IN {Conv.invalid, Conv.terminator} THEN 
    res:=strWrongFormat; rn:=0
  ELSIF prev=Conv.padding THEN 
    res:=strEmpty; rn:=0
  ELSE
    numb[pos]:=0X;
    Str.Insert(sign, 0, numb);   (* add the sign *) 
    res:=RC.FormatReal(numb);
    rn:=RC.ValueReal(numb)  
  END
END ValueMoneyRes;

PROCEDURE FormatMoney*(str: ARRAY OF CHAR): ConvResults;
  (* Returns the format of the string value for conversion to money. *)
VAR res: ConvResults; x: LONGREAL;
BEGIN
  ValueMoneyRes(str, x, res);
  RETURN res
END FormatMoney;
 
PROCEDURE ValueMoney*(str: ARRAY OF CHAR): LONGREAL;
VAR res: ConvResults; x: LONGREAL;
BEGIN
  ValueMoneyRes(str, x, res);
  RETURN x
END ValueMoney;

PROCEDURE Init;
BEGIN
  (* state machine initialization *)
  NEW(RS); NEW(P); NEW(F); NEW(SR);
  RS.p:=RSState; P.p:=PState; F.p:=FState; SR.p:=ScanNumber;
  
  NEW(RS2); NEW(P2); NEW(N2); NEW(F2); NEW(G2); NEW(SR2);
  RS2.p:=RS2State; P2.p:=P2State; F2.p:=F2State; 
  N2.p:=N2State; G2.p:=G2State; SR2.p:=ScanMoney 
END Init;

BEGIN
  Init 
END LocNumConv.
