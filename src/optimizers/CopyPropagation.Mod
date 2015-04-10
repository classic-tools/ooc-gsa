(* 	$Id: CopyPropagation.Mod,v 1.3 1999/03/15 18:54:42 acken Exp $	 *)
MODULE CopyPropagation;  (* Copyright (C) 1995  Juergen Zimmermann *)

IMPORT D := Data, Opc := Opcode;

PROCEDURE Propagate* (reg: D.Region);
  VAR
    instr, nextInstr: D.Instruction;
  BEGIN
    instr := reg. instrList;
    WHILE (instr # NIL) DO
      nextInstr := instr. nextInstr;
      IF (instr IS D.Region) THEN
        (* recursivly visit all embedded regions *)
        Propagate (instr(D.Region))
      ELSIF (instr. opcode = Opc.copy) THEN
        (* replace all uses of this 'copy' instruction by the first (and only)
           operand of the 'copy' instruction, then delete the 'copy' 
           instruction since it is dead code now  *)
        instr. ReplaceUses (instr. opndList. arg);
        instr. Delete()
      END;
      instr := nextInstr
    END
  END Propagate;
    
END CopyPropagation.


