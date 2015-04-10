(*	$Id: LocNumStr.Mod,v 1.3 1999/09/02 13:10:23 acken Exp $	*)
MODULE LocNumStr;

(*
    LocNumStr - Convert numbers to/from strings using locale information.
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

IMPORT CharClass, Conv:=ConvTypes, LRealStr, LocNumConv, Locales, Out:=OakOut, s:=Strings;

TYPE
  ConvResults * = Conv.ConvResults;
 
CONST
  strAllRight * = Conv.strAllRight;       (* no conversion problems *)
  strOutOfRange * = Conv.strOutOfRange;   (* string value is out of range *)
  strWrongFormat * = Conv.strWrongFormat; (* string is the wrong format *)
  strEmpty * = Conv.strEmpty;             (* string is empty *)
  
  DEBUG = FALSE;


PROCEDURE ExtractNum (VAR str: ARRAY OF CHAR) : INTEGER;
VAR
  num, pos: INTEGER; neg: BOOLEAN;
BEGIN
  num:=0;
  IF str[0]="-" THEN neg:=TRUE; pos:=1
  ELSE neg:=FALSE; pos:=0
  END;
  WHILE CharClass.IsNumeric(str[pos]) DO
    num:=num*10+ORD(str[0])-ORD("0"); INC(pos)
  END;
  IF str[pos]=";" THEN s.Delete(str, 0, pos+1) END;
  IF neg THEN RETURN -num ELSE RETURN num END
END ExtractNum;

PROCEDURE FormatStr (VAR str: ARRAY OF CHAR; dp, sep: CHAR;
                     grouping: ARRAY OF CHAR);
VAR
  pos, group: INTEGER; found: BOOLEAN;                     
BEGIN
  (* replace the decimal point *)
  s.FindNext(".", str, 0, found, pos);
  IF found THEN str[pos]:=dp ELSE pos:=s.Length(str) END;
  
  (* exit if no grouping data is present *) 
  IF (sep=0X) OR (grouping="") THEN RETURN END;
  
  (* apply the grouping separator information *)
  group:=3;  
  WHILE (group>0) & (pos>0) DO (* apply grouping information *)
    group:=ExtractNum(grouping);
    DEC(pos, group);
    IF pos>0 THEN s.Insert(grouping, pos, str) END  
  END 
END FormatStr;

PROCEDURE NumToStr * (num: LONGREAL; VAR str: ARRAY OF CHAR);
(* Converts the number in `num' to a localized number string in `str'. *)
VAR
  dp, sep: CHAR; 
  grouping: ARRAY 64 OF CHAR;
  ok: BOOLEAN;
BEGIN
  (* obtain the relevent locale information *)
  ok:=Locales.GetStr(Locales.decimalPoint, grouping); dp:=grouping[0];
  ok:=Locales.GetStr(Locales.thousandsSep, grouping); sep:=grouping[0];  
  ok:=Locales.GetStr(Locales.grouping, grouping);
  
  LRealStr.RealToStr(num, str);  (* just convert the number *) 
  FormatStr(str, dp, sep, grouping)
END NumToStr;

PROCEDURE MoneyToStr * (money: LONGREAL; int: BOOLEAN; 
                        VAR str: ARRAY OF CHAR);
(* Converts the number in `money' to a localized monetary string
   in `str'. When `int' is TRUE, the international localizations
   will be applied instead of the local standard. *)
VAR
  dp, sep: CHAR;
  sign, space: ARRAY 8 OF CHAR;
  grouping, curSym: ARRAY 64 OF CHAR;
  frac, spos: LONGINT;
  ok, precede: BOOLEAN;
BEGIN
  (* obtain the relevent locale information *)
  ok:=Locales.GetStr(Locales.monDecimalPoint, grouping); dp:=grouping[0];
  ok:=Locales.GetStr(Locales.monThousandsSep, grouping); sep:=grouping[0];
  ok:=Locales.GetStr(Locales.monGrouping, grouping);  
  
  IF int THEN
    (* extract international information *)
    ok:=Locales.GetStr(Locales.intCurrencySymbol, curSym);
    frac:=Locales.GetInt(Locales.intFracDigits)  
  ELSE
    (* extract local information *)
    ok:=Locales.GetStr(Locales.currencySymbol, curSym);
    frac:=Locales.GetInt(Locales.fracDigits)    
  END;
  IF frac=Locales.unspecified THEN frac:=-1 END;
  
  IF money<0 THEN
    (* extract negative money localization *)
    money:=-money;
    ok:=Locales.GetStr(Locales.negativeSign, sign);
    precede:=Locales.GetInt(Locales.nCSPrecedes)#0;
    IF ~int & (Locales.GetInt(Locales.nSepBySpace)#0) THEN space:=" "
    ELSE space:=""
    END;
    spos:=Locales.GetInt(Locales.nSignPosn)    
  ELSE
    (* extract positive money localization *)
    ok:=Locales.GetStr(Locales.positiveSign, sign);
    precede:=Locales.GetInt(Locales.pCSPrecedes)#0;
    IF ~int & (Locales.GetInt(Locales.pSepBySpace)#0) THEN space:=" "
    ELSE space:=""
    END;
    spos:=Locales.GetInt(Locales.pSignPosn)   
  END;  
  IF spos>=4 THEN spos:=4 END;
  
  (* finally format the money *)
  LRealStr.RealToFixed(money, SHORT(frac), str); 
  FormatStr(str, dp, sep, grouping);
  
  (* fix up the currency symbol *)
  IF precede THEN s.Append(space, curSym)  (* since number follows *)
  ELSE s.Insert(space, 0, curSym)          (* since number is first *)
  END;
  
  (* decide how to combine the sign, amount, and currency symbol *)
  CASE spos OF
  | 0: (* currency symbol and quantity surrounded by parentheses *)
       IF precede THEN s.Insert(curSym, 0, str)
       ELSE s.Append(curSym, str)
       END;
       s.Insert("(", 0, str); s.Append(")", str)
  | 1: (* sign before the quantity and currency symbol *)
       IF precede THEN s.Insert(curSym, 0, str); s.Insert(sign, 0, str)
       ELSE s.Append(curSym, str); s.Insert(sign, 0, str)
       END  
  | 2: (* sign after the quantity and currency symbol *)
       IF precede THEN s.Insert(curSym, 0, str); s.Append(sign, str)
       ELSE s.Append(curSym, str); s.Append(sign, str)
       END
  | 3: (* sign is right before the currency symbol *)
       s.Insert(sign, 0, curSym);
       IF precede THEN s.Insert(curSym, 0, str)
       ELSE s.Append(curSym, str)
       END       
  | ELSE (* sign is right after the currency symbol *)
       IF space="" THEN s.Append(sign, curSym)
       ELSIF curSym#" " THEN s.Insert(sign, s.Length(curSym)-2, curSym)
       ELSE s.Insert(sign, 0, curSym)
       END;
       IF precede THEN s.Insert(curSym, 0, str)
       ELSE s.Append(curSym, str)
       END        
  END
END MoneyToStr;

PROCEDURE StrToNum * (str: ARRAY OF CHAR; 
                      VAR num: LONGREAL; VAR res: ConvResults);
(* Returns a number in `num' for the localized number string 
   `str'.  `res' will contain an appropriate error code (see above)
   if the string conversion fails. For errors, `num' will take on
   the maximum legal value for strOutOfRange errors, and will be
   undefined for all other errors. *)
BEGIN
  res:=LocNumConv.FormatNumber(str);
  IF res IN {strAllRight, strOutOfRange} THEN num:=LocNumConv.ValueNumber(str) END
END StrToNum; 

PROCEDURE StrToMoney * (str: ARRAY OF CHAR; 
                        VAR money: LONGREAL; VAR res: ConvResults);
(* Returns a number in `money' for the localized monetary string 
   `str'.  `res' will contain an appropriate error code (see above)
   if the string conversion fails. For errors, `num' will take on
   the maximum legal value for strOutOfRange errors, and will be
   undefined for all other errors. *) 
BEGIN
  res:=LocNumConv.FormatNumber(str);
  IF res IN {strAllRight, strOutOfRange} THEN money:=LocNumConv.ValueNumber(str) END
END StrToMoney;


PROCEDURE Test;
VAR
  num: LONGREAL;
  res: ConvResults;
  str: ARRAY 128 OF CHAR;
BEGIN
  Locales.Set(Locales.ALL, "", str);
  MoneyToStr(2000.0, TRUE, str); Out.String(str); Out.Ln;
  MoneyToStr(2000.0, FALSE, str); Out.String(str); Out.Ln;
  NumToStr(2000.0, str); Out.String(str); Out.Ln;
  StrToMoney("$ 2,000.00", num, res); 
  IF res=strAllRight THEN Out.LongReal(num, 1)
  ELSE Out.String("Illegal money...")
  END;
  Out.Ln;
END Test;

BEGIN
  IF DEBUG THEN Test END
END LocNumStr.
