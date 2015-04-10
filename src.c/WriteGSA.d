/* file generated by oo2c -- do not edit */
#include "WriteGSA.h"
#include "IntStr.h"
#include "Opcode.h"
#include "Out.h"
#include "Strings.h"
#include "WriteSymbols.h"

/* local definitions */
static ParamOptions__BooleanOption WriteGSA__writeInstrPos;
static ParamOptions__BooleanOption WriteGSA__writeOpndPos;
static ParamOptions__BooleanOption WriteGSA__writeGateOld;
ParamOptions__BooleanOption WriteGSA__writeAssignHints;
ParamOptions__BooleanOption WriteGSA__writeQualNames;
static Data__Object WriteGSA__mod;

/* function prototypes */
void WriteGSA__Id(int off, int marker, int pos);
void WriteGSA__Name(Data__Addressable a, unsigned char* str, int str_0d);
void WriteGSA__Argument(Data__Info i, unsigned char* str, int str_0d);
void WriteGSA__Location(Data__Location loc, unsigned char* str, int str_0d);
void WriteGSA__Subclass(short int scode, unsigned char* str, int str_0d);
void WriteGSA__Opcode_Operator(short int opcode, unsigned char* str, int str_0d);
void WriteGSA__Opcode_AccessSubclass(short int opcode, unsigned char* str, int str_0d);
void WriteGSA__WrLocation(Data__Location loc);
void WriteGSA__WrSubclass(short int opc);
void WriteGSA__WrOperands(Data__Instruction instr);
void WriteGSA__WrResults(Data__Instruction instr);
void WriteGSA__WrFlags(Data__Instruction instr);
void WriteGSA__WrInstr(Data__Instruction instr, short int off);
void WriteGSA__SetMarkers_MarkInstr(Data__Instruction instr, int *WriteGSA__SetMarkers_counter);
void WriteGSA__SetMarkers(Data__Region greg);
void WriteGSA__SetMarkersPos_MarkInstr(Data__Instruction instr, int *WriteGSA__SetMarkersPos_counter);

/* module and type descriptors */
static const struct {
  int length;
  void* pad;
  const void* list[7];
} _p0 = {7, NULL, {
  (const void*)&WriteGSA__Body,
  (const void*)&WriteGSA__Class,
  (const void*)&WriteGSA__MW,
  (const void*)&WriteGSA__Opcode,
  (const void*)&WriteGSA__SetMarkersPos,
  (const void*)&WriteGSA__WrArgument,
  (const void*)&WriteGSA__WrOpcode,
}};
static const struct {
  int length;
  void* pad;
  const void* list[2];
} _p1 = {2, NULL, {
  (const void*)&WriteGSA__writeAssignHints,
  (const void*)&WriteGSA__writeQualNames,
}};
static const struct {
  int length;
  void* pad;
  const char name[9];
} _n0 = {9, NULL, {"WriteGSA"}};
static struct _MD WriteGSA_md = {
  NULL, 
  &Kernel__ModuleDesc_td.td, 
  {
    NULL, 
    (const unsigned char*)_n0.name, 
    -1, 
    NULL,
    _p0.list,
    _p1.list,
    16251308
  }
};

/* local strings */
static const unsigned char _c151[] = "writeQualNames:=TRUE";
static const unsigned char _c150[] = "--gsa-qnames";
static const unsigned char _c149[] = "writeQualNames";
static const unsigned char _c148[] = "writeAssignHints:=TRUE";
static const unsigned char _c147[] = "--gsa-assign";
static const unsigned char _c146[] = "writeAssignHints";
static const unsigned char _c145[] = "writeGateOld:=TRUE";
static const unsigned char _c144[] = "--gsa-gate-old";
static const unsigned char _c143[] = "writeGateOld";
static const unsigned char _c142[] = "writeOpndPos:=TRUE";
static const unsigned char _c141[] = "--gsa-opnd-pos";
static const unsigned char _c140[] = "writeOpndPos";
static const unsigned char _c139[] = "writeInstrPos:=TRUE";
static const unsigned char _c138[] = "--gsa-instr-pos";
static const unsigned char _c137[] = "writeInstrPos";
static const unsigned char _c136[] = "module body: ";
static const unsigned char _c135[] = "procedure ";
static const unsigned char _c134[] = " poisonHeap";
static const unsigned char _c133[] = " guardFor";
static const unsigned char _c132[] = " uniqueResult";
static const unsigned char _c131[] = " stackCheck";
static const unsigned char _c130[] = " initialize";
static const unsigned char _c129[] = " checkDiv";
static const unsigned char _c128[] = " checkNil";
static const unsigned char _c127[] = " checkOverflow";
static const unsigned char _c126[] = " isDisabled";
static const unsigned char _c125[] = " notDead";
static const unsigned char _c124[] = "    [flags:";
static const unsigned char _c123[] = " := ";
static const unsigned char _c122[] = "res.";
static const unsigned char _c121[] = "..";
static const unsigned char _c120[] = "<type ";
static const unsigned char _c119[] = "[XXX]";
static const unsigned char _c118[] = ", ";
static const unsigned char _c117[] = " ";
static const unsigned char _c116[] = "> ";
static const unsigned char _c115[] = "NIL";
static const unsigned char _c114[] = " <";
static const unsigned char _c113[] = "trap-with";
static const unsigned char _c112[] = "trap-halt";
static const unsigned char _c111[] = "trap-assert";
static const unsigned char _c110[] = "trap-case";
static const unsigned char _c109[] = "trap-return";
static const unsigned char _c108[] = "merge-case:";
static const unsigned char _c107[] = "merge-loop:";
static const unsigned char _c106[] = "merge-cond:";
static const unsigned char _c105[] = "merge-if:";
static const unsigned char _c104[] = "if-member:";
static const unsigned char _c103[] = "greg:";
static const unsigned char _c102[] = "if-false:";
static const unsigned char _c101[] = "if-true:";
static const unsigned char _c100[] = "update-";
static const unsigned char _c99[] = "access-";
static const unsigned char _c98[] = "zero";
static const unsigned char _c97[] = "delete-store";
static const unsigned char _c96[] = "create-store";
static const unsigned char _c95[] = "move";
static const unsigned char _c94[] = "new-block";
static const unsigned char _c93[] = "new";
static const unsigned char _c92[] = "struct-copy";
static const unsigned char _c91[] = "string-copy";
static const unsigned char _c90[] = "type-cast";
static const unsigned char _c89[] = "bit";
static const unsigned char _c88[] = "type-assert";
static const unsigned char _c87[] = "type-guard";
static const unsigned char _c86[] = "type-test";
static const unsigned char _c85[] = "tb-proc-adr";
static const unsigned char _c84[] = "type-tag";
static const unsigned char _c83[] = "array-length";
static const unsigned char _c82[] = "call";
static const unsigned char _c81[] = "bound-range";
static const unsigned char _c80[] = "bound-index";
static const unsigned char _c79[] = "gate";
static const unsigned char _c78[] = "copy";
static const unsigned char _c77[] = "adr";
static const unsigned char _c76[] = "exit";
static const unsigned char _c75[] = "enter";
static const unsigned char _c74[] = "\077opc";
static const unsigned char _c73[] = "mem";
static const unsigned char _c72[] = "var-param";
static const unsigned char _c71[] = "nonlocal";
static const unsigned char _c70[] = "heap";
static const unsigned char _c69[] = "element";
static const unsigned char _c68[] = "field";
static const unsigned char _c67[] = "geq";
static const unsigned char _c66[] = "gtr";
static const unsigned char _c65[] = "leq";
static const unsigned char _c64[] = "lss";
static const unsigned char _c63[] = "neq";
static const unsigned char _c62[] = "eql";
static const unsigned char _c61[] = "rot";
static const unsigned char _c60[] = "lsh";
static const unsigned char _c59[] = "odd";
static const unsigned char _c58[] = "cap";
static const unsigned char _c57[] = "ash";
static const unsigned char _c56[] = "abs";
static const unsigned char _c55[] = "not";
static const unsigned char _c54[] = "bittest";
static const unsigned char _c53[] = "bitrange";
static const unsigned char _c52[] = "bitclear";
static const unsigned char _c51[] = "bitset";
static const unsigned char _c50[] = "compl";
static const unsigned char _c49[] = "diff";
static const unsigned char _c48[] = "union";
static const unsigned char _c47[] = "symdiff";
static const unsigned char _c46[] = "inter";
static const unsigned char _c45[] = "neg";
static const unsigned char _c44[] = "mod";
static const unsigned char _c43[] = "divi";
static const unsigned char _c42[] = "divr";
static const unsigned char _c41[] = "mult";
static const unsigned char _c40[] = "sub";
static const unsigned char _c39[] = "add";
static const unsigned char _c38[] = "conv";
static const unsigned char _c37[] = "trap";
static const unsigned char _c36[] = "merge";
static const unsigned char _c35[] = "guard";
static const unsigned char _c34[] = "update";
static const unsigned char _c33[] = "access";
static const unsigned char _c32[] = "special";
static const unsigned char _c31[] = "lstr";
static const unsigned char _c30[] = "str";
static const unsigned char _c29[] = "d";
static const unsigned char _c28[] = "r";
static const unsigned char _c27[] = "llu";
static const unsigned char _c26[] = "ll";
static const unsigned char _c25[] = "lu";
static const unsigned char _c24[] = "l";
static const unsigned char _c23[] = "iu";
static const unsigned char _c22[] = "i";
static const unsigned char _c21[] = "su";
static const unsigned char _c20[] = "s";
static const unsigned char _c19[] = "\077";
static const unsigned char _c18[] = "_";
static const unsigned char _c17[] = "";
static const unsigned char _c16[] = "/tag";
static const unsigned char _c15[] = "/adr";
static const unsigned char _c14[] = "/len";
static const unsigned char _c13[] = "\077\077";
static const unsigned char _c12[] = ".0";
static const unsigned char _c11[] = "()";
static const unsigned char _c10[] = ".\077";
static const unsigned char _c9[] = "<fpar>";
static const unsigned char _c8[] = "<field>";
static const unsigned char _c7[] = "<tb_proc>";
static const unsigned char _c6[] = ".";
static const unsigned char _c5[] = "<anon_struct>";
static const unsigned char _c4[] = ") ";
static const unsigned char _c3[] = "  ";
static const unsigned char _c2[] = "[XXX]   ";
static const unsigned char _c1[] = "[XXX] ";
static const unsigned char _c0[] = "] ";

