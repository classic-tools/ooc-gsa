/* file generated by oo2c -- do not edit */
#include "Attributes.h"
#include "Error.h"
#include "Opcode.h"
#include "Scanner.h"
#include "StdPragmas.h"
#include "StdTypes.h"
#include "SymbolTable.h"

/* local definitions */

/* function prototypes */
void Attributes__InitGreg_Parameter(Data__Object obj, Data__GlobalRegion *Attributes__InitGreg_greg);
Data__Instruction Attributes__InitGreg_CreateFalse(Data__GlobalRegion *Attributes__InitGreg_greg);
unsigned char Attributes__TracesToEmptyStore_ModifiedVarParam(Data__Object var, Data__Instruction call);
Data__Usable Attributes__TypeTag_TypeDescrAdr(Data__Struct type, Attributes__Item *Attributes__TypeTag_x, Data__Region *Attributes__TypeTag_region);
Data__Const Attributes__ArrayLength_GetConst(int value, unsigned char *Attributes__ArrayLength_adaptType);
Data__Usable Attributes__SizeOfItem_Mult(Data__Usable opnd0, Data__Usable opnd1, Data__Region *Attributes__SizeOfItem_region, int *Attributes__SizeOfItem_pos);
short int Attributes__GetNonParamOpnd_OpndCount(Data__Object formal);
Data__Opnd Attributes__GetNonParamOpnd_SkipOpnds(short int n, Data__Opnd opndList);
void Attributes__CleanupGreg_ScanUpdates(Data__Object obj);
void Attributes__CleanupGreg_RemoveNoopGateHints(Data__Region r);

/* module and type descriptors */
static const struct {
  int length;
  void* pad;
  const void* list[25];
} _p0 = {25, NULL, {
  (const void*)&Attributes__Address,
  (const void*)&Attributes__Adr,
  (const void*)&Attributes__ArrayLength,
  (const void*)&Attributes__CleanupGreg,
  (const void*)&Attributes__ContainsRuntimeCheck,
  (const void*)&Attributes__CreateGreg,
  (const void*)&Attributes__CreateGuard,
  (const void*)&Attributes__CreateItem,
  (const void*)&Attributes__DyadicOp,
  (const void*)&Attributes__ExitInfoOr,
  (const void*)&Attributes__FindAddEnterResult,
  (const void*)&Attributes__GetNonParamOpnd,
  (const void*)&Attributes__GuardExit,
  (const void*)&Attributes__HasLengthInfo,
  (const void*)&Attributes__InitExitInfo,
  (const void*)&Attributes__InitGreg,
  (const void*)&Attributes__InitItem,
  (const void*)&Attributes__Operand,
  (const void*)&Attributes__PartOfStore,
  (const void*)&Attributes__SetOpndPos,
  (const void*)&Attributes__SizeOfItem,
  (const void*)&Attributes__TBProcAdr,
  (const void*)&Attributes__TracesToEmptyStore,
  (const void*)&Attributes__TypeTag,
  (const void*)&Attributes__UnguardExit,
}};
static const struct {
  int length;
  void* pad;
  const void* list[0];
} _p1 = {0, NULL, {
}};
static const struct {
  int length;
  void* pad;
  const char name[11];
} _n0 = {11, NULL, {"Attributes"}};
static struct _MD Attributes_md = {
  NULL, 
  &Kernel__ModuleDesc_td.td, 
  {
    NULL, 
    (const unsigned char*)_n0.name, 
    -1, 
    NULL,
    _p0.list,
    _p1.list,
    -801218519
  }
};

static const struct {
  int length;
  void* pad;
  const char name[5];
} _n1 = {5, NULL, {"Item"}};
static const struct {
  int length;
  void* pad;
  _Type btypes[1];
} Attributes__Item_tdb = {
  1, 
  NULL, 
  {
    &Attributes__Item_td.td
  }
};
static const struct {
  int length;
  void* pad;
  const void* tbprocs[1];
} _tb0 = {0, NULL, {
  NULL
}};
struct _TD Attributes__Item_td = {
  NULL,
  &Types__TypeDesc_td.td,
  {
    Attributes__Item_tdb.btypes,
    _tb0.tbprocs,
    (const unsigned char*)_n1.name,
    &Attributes_md.md,
    0, 
    '0', '1',
    sizeof(Attributes__Item),
    NULL
  }
};

static const struct {
  int length;
  void* pad;
  const char name[9];
} _n2 = {9, NULL, {"ExitInfo"}};
static const struct {
  int length;
  void* pad;
  _Type btypes[1];
} Attributes__ExitInfo_tdb = {
  1, 
  NULL, 
  {
    &Attributes__ExitInfo_td.td
  }
};
static const struct {
  int length;
  void* pad;
  const void* tbprocs[1];
} _tb1 = {0, NULL, {
  NULL
}};
struct _TD Attributes__ExitInfo_td = {
  NULL,
  &Types__TypeDesc_td.td,
  {
    Attributes__ExitInfo_tdb.btypes,
    _tb1.tbprocs,
    (const unsigned char*)_n2.name,
    &Attributes_md.md,
    0, 
    '0', '1',
    sizeof(Attributes__ExitInfo),
    &Attributes__Item_td.td
  }
};

/* local strings */
static const unsigned char _c2[] = "$result";
static const unsigned char _c1[] = "$trap";
static const unsigned char _c0[] = "$return";

