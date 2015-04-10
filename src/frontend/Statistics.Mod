(*	$Id: Statistics.Mod,v 1.11 1999/07/30 21:11:21 acken Exp $	*)
MODULE Statistics;
(*  Frequency count of instruction, results, and operands in GSA code.
    Copyright (C) 1997-1999  Michael van Acken

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

(* Determines frequency of instructions/classes in GSA code.  *)

IMPORT
  Strings, Out, IntStr, RealStr, LRealStr, 
  D := Data, Opc := Opcode, WriteGSA; 
  
  
CONST
  numClass = Opc.classGeq+1;
  numInstr = numClass*Opc.sizeClass;

  widthClass = 9;
  widthOpcode = 17;
  widthFreq = 18;
  widthDiff = 9;
  
TYPE
  Counter* = RECORD
    total: LONGINT;
    instr: ARRAY numInstr OF LONGINT;
    class: ARRAY numClass OF LONGINT;
    instrCount,                          (* instructions without regions *)
    resultCount,                         (* results without instructions *)
    opndCount, 
    regionCount: LONGINT;
  END;


PROCEDURE (VAR c: Counter) Clear*;
  VAR
    i: INTEGER;
  BEGIN
    c. total := 0;
    FOR i := 0 TO numInstr-1 DO
      c. instr[i] := 0
    END;
    FOR i := 0 TO numClass-1 DO
      c. class[i] := 0
    END;
    c. instrCount := 0;
    c. resultCount := 0;
    c. opndCount := 0;
    c. regionCount := 0;
  END Clear;

PROCEDURE (VAR c1: Counter) Add* (VAR c2: Counter);
  VAR
    i: INTEGER;
  BEGIN
    INC (c1. total, c2. total);
    FOR i := 0 TO numInstr-1 DO
      INC (c1. instr[i], c2. instr[i])
    END;
    FOR i := 0 TO numClass-1 DO
      INC (c1. class[i], c2. class[i])
    END;
    INC (c1. instrCount, c2. instrCount);
    INC (c1. resultCount, c2. resultCount);
    INC (c1. opndCount, c2. opndCount);
    INC (c1. regionCount, c2. regionCount)
  END Add;

PROCEDURE (VAR c: Counter) AddRegion* (region: D.Region);
  VAR
    instr: D.Instruction;
    result: D.Result;
    opnd: D.Opnd;
  BEGIN
    instr := region. instrList;
    WHILE (instr # NIL) DO
      INC (c. total);
      INC (c. instr[instr. opcode]);
      INC (c. class[instr. opcode DIV Opc.sizeClass]);
      IF (instr IS D.Region) THEN
        INC (c. regionCount);
        c. AddRegion (instr(D.Region))
      ELSE
        INC (c. instrCount)
      END;
      
      result := instr. nextResult;
      WHILE (result # NIL) DO
        INC (c. resultCount);
        result := result. nextResult
      END;
      opnd := instr. opndList;
      WHILE (opnd # NIL) DO
        INC (c. opndCount);
        opnd := opnd. nextOpnd
      END;
      
      instr := instr. nextInstr
    END
  END AddRegion;

PROCEDURE (VAR c: Counter) CountRegion* (region: D.Region);
  BEGIN
    c. Clear;
    c. AddRegion (region)
  END CountRegion;


PROCEDURE PadLeft (VAR str: ARRAY OF CHAR; width: INTEGER);
  VAR
    blanks: ARRAY 128 OF CHAR;
    i, len: INTEGER;
  BEGIN
    len := Strings.Length (str);
    IF (width > len) THEN
      FOR i := 0 TO width-len-1 DO
        blanks[i] := " "
      END;
      blanks[width-len] := 0X;
      Strings.Insert (blanks, 0, str)
    END
  END PadLeft;

PROCEDURE Padding (count: INTEGER);
  BEGIN
    WHILE (count > 0) DO
      Out.Char (" ");
      DEC (count)
    END
  END Padding;

PROCEDURE Sep (count: INTEGER);
  BEGIN
    WHILE (count > 0) DO
      Out.Char ("-");
      DEC (count)
    END
  END Sep;

PROCEDURE WrFrequency (count, total: LONGINT; width: INTEGER);
  VAR
    str, p: ARRAY 128 OF CHAR;
  BEGIN
    IntStr.IntToStr (count, str);
    Strings.Append ("  (", str);
    RealStr.RealToFixed ((count / total) * 100, 2, p);
    PadLeft (p, 6);
    Strings.Append (p, str);
    Strings.Append ("%)", str);
    PadLeft (str, width);
    Out.String (str)
  END WrFrequency;

PROCEDURE WrDiff (a, b: LONGINT; width: INTEGER);
  VAR
    d: LONGINT;
    abs, rel: ARRAY 32 OF CHAR;
  BEGIN
    d := b-a;
    IntStr.IntToStr (d, abs);
    IF (d > 0) THEN
      Strings.Insert ("+", 0, abs)
    END;
    PadLeft (abs, width);
    Out.String (abs);
    
    IF (d # 0) & (a # 0) THEN
      LRealStr.RealToFixed (d * 100.0D0 / a, 2, rel);
      IF (d > 0) THEN
        Strings.Insert ("+", 0, rel)
      END;
      Out.String ("  ");
      Out.String (rel);
      Out.Char ("%")
    END
  END WrDiff;

PROCEDURE WrTotal (entries: INTEGER; sum, total: LONGINT; width1, width2: INTEGER);
  VAR
    str: ARRAY 128 OF CHAR;
  BEGIN
    Sep (width1+width2);
    Out.Ln;
    Out.LongInt (entries, width1-1);
    Out.Char (" ");
    WrFrequency (sum, total, width2)
  END WrTotal;

PROCEDURE (VAR c: Counter) WrClasses (order: ARRAY OF INTEGER; entries: INTEGER);
  VAR
    i: INTEGER;
    sum: LONGINT;
    str: ARRAY 128 OF CHAR;
  BEGIN
    IF (c. total # 0) THEN
      Out.String ("class frequency listing; total="); 
      Out.LongInt (c. total, 0); 
      Out.String (" instructions"); Out.Ln;
      sum := 0;
      FOR i := 0 TO entries-1 DO
        WriteGSA.Class (order[i], str);
        PadLeft (str, widthClass-1);
        Out.String (str); Out.Char (" ");
        WrFrequency (c. class[order [i]], c. total, widthFreq);
        INC (sum, c. class[order [i]]);
        Out.Ln
      END;
      WrTotal (entries, sum, c. total, widthClass, widthFreq);
      Out.Ln
    END
  END WrClasses;

PROCEDURE (VAR c: Counter) WrInstructions (order: ARRAY OF INTEGER; entries: INTEGER);
  VAR
    i: INTEGER;
    sum: LONGINT;
    str: ARRAY 128 OF CHAR;
  BEGIN
    IF (c. total # 0) THEN
      Out.String ("instruction frequency listing; total="); 
      Out.LongInt (c. total, 0); 
      Out.String (" instructions"); Out.Ln;
      sum := 0;
      FOR i := 0 TO entries-1 DO
        WriteGSA.Opcode (order[i], str);
        PadLeft (str, widthOpcode-1);
        Out.String (str); Out.Char (" ");
        WrFrequency (c. instr[order [i]], c. total, widthFreq);
        INC (sum, c. instr[order [i]]);
        Out.Ln
      END;
      WrTotal (entries, sum, c. total, widthOpcode, widthFreq);
      Out.Ln
    END
  END WrInstructions;

PROCEDURE Sort (keys: ARRAY OF LONGINT; VAR permutation: ARRAY OF INTEGER): INTEGER;
  VAR
    i, entries: INTEGER;
  
  PROCEDURE Quick (l, r: INTEGER);
    VAR
      i, j, max: INTEGER;
      v: LONGINT;
    
    PROCEDURE Swap (i, j: INTEGER);
      VAR
        x: INTEGER;
      BEGIN
        x := permutation[i];
        permutation[i] := permutation[j];
        permutation[j] := x
      END Swap;
    
    BEGIN
      IF (l+8 > r) THEN  (* selection sort *)
        FOR i := l TO r DO
          max := i;
          FOR j := i+1 TO r DO
            IF (keys[permutation[j]] > keys[permutation[max]]) THEN
              max := j
            END
          END;
          Swap (i, max)
        END
      ELSE  (* quick sort *)
        i := l-1; j := r; 
        Swap ((l+r) DIV 2, r);
        v := keys[permutation[r]];
        LOOP
          REPEAT 
            INC (i)
          UNTIL (i = r) OR (keys[permutation[i]] <= v);
          REPEAT
            DEC (j)
          UNTIL (j = l) OR (keys[permutation[j]] >= v);
          IF (i >= j) THEN
            EXIT
          END;
          Swap (i, j)
        END;
        Swap (i, r);
        Quick (l, j); Quick (i+1, r)
      END
    END Quick;
  
  BEGIN
    ASSERT (LEN (keys) = LEN (permutation));
    (* fill permutation array with identity mapping *)
    FOR i := 0 TO SHORT (LEN (keys))-1 DO
      permutation[i] := i
    END;
    (* sort keys, larger keys first *)
    Quick (0, SHORT (LEN (keys))-1);
    (* count non-zero entries *)
    entries := 0;
    WHILE (entries # LEN (keys)) & (keys[permutation[entries]] # 0) DO
      INC (entries)
    END;
    RETURN entries
  END Sort;

PROCEDURE (VAR c: Counter) WriteSortedClasses*;
  VAR
    perm: ARRAY numClass OF INTEGER;
    entries: INTEGER;
  BEGIN
    entries := Sort (c. class, perm);
    c. WrClasses (perm, entries)
  END WriteSortedClasses;

PROCEDURE (VAR c1: Counter) WriteDiffClasses* (text1: ARRAY OF CHAR; VAR c2: Counter; text2: ARRAY OF CHAR);
  VAR
    c3: Counter;
    str: ARRAY 128 OF CHAR;
    perm: ARRAY numClass OF INTEGER;
    entries, i: INTEGER;
    sum1, sum2: LONGINT;
  BEGIN
    IF (c1. total # 0) OR (c2. total # 0) THEN
      c3 := c1;
      c3. Add (c2);
      entries := Sort (c3. class, perm);
      
      Out.String ("class difference listing"); Out.Ln;
      Padding (widthClass);
      Out.String (text1); Padding (widthFreq-Strings.Length (text1)); 
      Out.String (" | ");
      Out.String (text2); Padding (widthFreq-Strings.Length (text2)); 
      Out.String (" | ");
      Out.String ("difference (abs rel)");
      Out.Ln;
      sum1 := 0; sum2 := 0;
      FOR i := 0 TO entries-1 DO
        WriteGSA.Class (perm[i], str);
        PadLeft (str, widthClass-1);
        Out.String (str); Out.Char (" ");
        WrFrequency (c1. class[perm [i]], c1. total, widthFreq);
        INC (sum1, c1. class[perm [i]]);
        Out.String (" | ");
        WrFrequency (c2. class[perm [i]], c2. total, widthFreq);
        INC (sum2, c2. class[perm [i]]);
        Out.String (" | ");
        WrDiff (c1. class[perm [i]], c2. class[perm [i]], widthDiff);
        Out.Ln
      END;
      
      Sep (widthClass+widthFreq+3+widthFreq+3+widthDiff+9); Out.Ln;
      Out.LongInt (entries, widthClass-1);
      Out.String (str); Out.Char (" ");
      WrFrequency (sum1, c1. total, widthFreq);
      Out.String (" | "); 
      WrFrequency (sum2, c2. total, widthFreq);
      Out.String (" | "); 
      WrDiff (sum1, sum2, widthDiff);
      Out.Ln
    END
  END WriteDiffClasses;
  
PROCEDURE (VAR c: Counter) WriteSortedInstructions*;
  VAR
    perm: ARRAY numInstr OF INTEGER;
    entries: INTEGER;
  BEGIN
    entries := Sort (c. instr, perm);
    c. WrInstructions (perm, entries)
  END WriteSortedInstructions;

PROCEDURE (VAR c1: Counter) WriteDiffInstructions* (text1: ARRAY OF CHAR; VAR c2: Counter; text2: ARRAY OF CHAR);
  VAR
    c3: Counter;
    str: ARRAY 128 OF CHAR;
    perm: ARRAY numInstr OF INTEGER;
    entries, i: INTEGER;
    sum1, sum2: LONGINT;
  BEGIN
    IF (c1. total # 0) OR (c2. total # 0) THEN
      c3 := c1;
      c3. Add (c2);
      entries := Sort (c3. instr, perm);
      
      Out.String ("instruction difference listing"); Out.Ln;
      Padding (widthOpcode);
      Out.String (text1); Padding (widthFreq-Strings.Length (text1)); 
      Out.String (" | ");
      Out.String (text2); Padding (widthFreq-Strings.Length (text2)); 
      Out.String (" | ");
      Out.String ("difference (abs rel)");
      Out.Ln;
      sum1 := 0; sum2 := 0;
      FOR i := 0 TO entries-1 DO
        WriteGSA.Opcode (perm[i], str);
        PadLeft (str, widthOpcode-1);
        Out.String (str); Out.Char (" ");
        WrFrequency (c1. instr[perm [i]], c1. total, widthFreq);
        INC (sum1, c1. instr[perm [i]]);
        Out.String (" | ");
        WrFrequency (c2. instr[perm [i]], c2. total, widthFreq);
        INC (sum2, c2. instr[perm [i]]);
        Out.String (" | ");
        WrDiff (c1. instr[perm [i]], c2. instr[perm [i]], widthDiff);
        Out.Ln
      END;
      
      Sep (widthOpcode+widthFreq+3+widthFreq+3+widthDiff+9); Out.Ln;
      Out.LongInt (entries, widthOpcode-1);
      Out.Char (" ");
      WrFrequency (sum1, c1. total, widthFreq);
      Out.String (" | "); 
      WrFrequency (sum2, c2. total, widthFreq);
      Out.String (" | "); 
      WrDiff (sum1, sum2, widthDiff);
      Out.Ln
    END
  END WriteDiffInstructions;
  
PROCEDURE (VAR c: Counter) WriteCounters*;
  BEGIN
    Out.String ("  regions    : "); Out.LongInt (c. regionCount, 0); Out.Ln;
    Out.String ("  intructions: "); Out.LongInt (c. instrCount, 0); Out.Ln;
    Out.String ("  operands   : "); Out.LongInt (c. opndCount, 0); Out.Ln;
    Out.String ("  results    : "); Out.LongInt (c. resultCount, 0); Out.Ln
  END WriteCounters;

END Statistics.
