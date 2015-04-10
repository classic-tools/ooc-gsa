/* file generated by oo2c -- do not edit */
#include "ValueNumbering.h"
#include "Opcode.h"
#include "Worklist.h"

/* local definitions */
typedef ValueNumbering__Partition ValueNumbering__PartitionList;
static ValueNumbering__Partition ValueNumbering__partitionList;
static ValueNumbering__Partition ValueNumbering__sizeOnePartitions;
static ValueNumbering__Partition ValueNumbering__collectPartitions[592];
typedef void(* ValueNumbering__MoveDifferentProc)(ValueNumbering__Partition current, ValueNumbering__Partition *created);

/* function prototypes */
ValueNumbering__InstrNode ValueNumbering__NewInstrNode(Data__Instruction instr);
ValueNumbering__Partition ValueNumbering__NewPartition(ValueNumbering__Partition super);
unsigned char ValueNumbering__SameOperandArgument(Data__Opnd opnd1, Data__Opnd opnd2);
unsigned char ValueNumbering__OwnPartitionAsDefault(Data__Instruction instr);
unsigned char ValueNumbering__Available(Data__Instruction res, Data__Region reg);
void ValueNumbering__AddToWorklistUnique(ValueNumbering__Partition *worklist, ValueNumbering__Partition part);
void ValueNumbering__ClearWorklist(ValueNumbering__Partition *worklist);
unsigned char ValueNumbering__PartitionInWorklist(ValueNumbering__Partition part, ValueNumbering__Partition worklist);
void ValueNumbering__Normalize(Data__Region reg);
void ValueNumbering__MarkLoopDependentInstr_AddUsingInstrUniqueIn(Worklist__Worklist *wl, _Type wl__tag, Data__Result used, Data__Merge merge);
void ValueNumbering__MarkLoopDependentInstr(Data__Region reg);
void ValueNumbering__InitCollectPartitions(void);
void ValueNumbering__ClassifyInstructions_IncludeInPartition(Data__Instruction instr);
void ValueNumbering__ClassifyInstructions(Data__Region reg);
void ValueNumbering__CollectNonEmptyPartitions(void);
void ValueNumbering__PartitionByPredicate(ValueNumbering__MoveDifferentProc mdp);
void ValueNumbering__MoveDifferentSignature_MoveInstrIntoOwnPartition(ValueNumbering__Partition current, ValueNumbering__Partition *created);
void ValueNumbering__MoveDifferentSignature(ValueNumbering__Partition current, ValueNumbering__Partition *created);
void ValueNumbering__PartitionBySignature(void);
void ValueNumbering__MoveDifferentOperand(ValueNumbering__Partition current, ValueNumbering__Partition *created);
void ValueNumbering__PartitionByOperand(void);
void ValueNumbering__MoveDifferentLoopDependence(ValueNumbering__Partition current, ValueNumbering__Partition *created);
void ValueNumbering__PartitionByLoopDependence(void);
void ValueNumbering__MoveNotAvailable(ValueNumbering__Partition current, ValueNumbering__Partition *created);
void ValueNumbering__PartitionByAvailability(void);
void ValueNumbering__StripUnusedPartitions(ValueNumbering__Partition *partitionList, ValueNumbering__Partition *sizeOnePartitions);
int ValueNumbering__GetMaxOpndPos(ValueNumbering__InstrList instrList);
void ValueNumbering__GetSplittedPartitions(ValueNumbering__Partition *splittedPartitions, ValueNumbering__InstrList instrList, int opndPos);
unsigned char ValueNumbering__HasOpndAtIn(Data__Instruction instr, int at, ValueNumbering__InstrList in);
void ValueNumbering__SplitPartitions_SplitByPartition_SplitPartitionByAt(ValueNumbering__Partition split, ValueNumbering__Partition by, int at, ValueNumbering__InstrList instrList, ValueNumbering__Partition *ValueNumbering__SplitPartitions_SplitByPartition_created, unsigned char *ValueNumbering__SplitPartitions_fixpoint);
void ValueNumbering__SplitPartitions_SplitByPartition(ValueNumbering__Partition splittingPart, ValueNumbering__Partition *created, ValueNumbering__Partition *ValueNumbering__SplitPartitions_current, unsigned char *ValueNumbering__SplitPartitions_fixpoint);
void ValueNumbering__SplitPartitions(void);
void ValueNumbering__CSE_Eliminate(ValueNumbering__Partition part, ValueNumbering__Partition *ValueNumbering__CSE_other);
void ValueNumbering__CSE(void);

/* module and type descriptors */
static const struct {
  int length;
  void* pad;
  const void* list[1];
} _p0 = {1, NULL, {
  (const void*)&ValueNumbering__Number,
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
  const char name[15];
} _n0 = {15, NULL, {"ValueNumbering"}};
static struct _MD ValueNumbering_md = {
  NULL, 
  &Kernel__ModuleDesc_td.td, 
  {
    NULL, 
    (const unsigned char*)_n0.name, 
    -1, 
    NULL,
    _p0.list,
    _p1.list,
    231942598
  }
};

static const struct {
  int length;
  void* pad;
  const char name[14];
} _n1 = {14, NULL, {"InstrListDesc"}};
static const struct {
  int length;
  void* pad;
  _Type btypes[1];
} ValueNumbering__InstrListDesc_tdb = {
  1, 
  NULL, 
  {
    &ValueNumbering__InstrListDesc_td.td
  }
};
static const struct {
  int length;
  void* pad;
  const void* tbprocs[1];
} _tb0 = {0, NULL, {
  NULL
}};
struct _TD ValueNumbering__InstrListDesc_td = {
  NULL,
  &Types__TypeDesc_td.td,
  {
    ValueNumbering__InstrListDesc_tdb.btypes,
    _tb0.tbprocs,
    (const unsigned char*)_n1.name,
    &ValueNumbering_md.md,
    0, 
    '0', '1',
    sizeof(ValueNumbering__InstrListDesc),
    NULL
  }
};

static const struct {
  int length;
  void* pad;
  const char name[14];
} _n2 = {14, NULL, {"PartitionDesc"}};
static const struct {
  int length;
  void* pad;
  _Type btypes[1];
} ValueNumbering__PartitionDesc_tdb = {
  1, 
  NULL, 
  {
    &ValueNumbering__PartitionDesc_td.td
  }
};
static const struct {
  int length;
  void* pad;
  const void* tbprocs[7];
} _tb1 = {7, NULL, {
  (void*)ValueNumbering__PartitionDesc_Concatenate, 
  (void*)ValueNumbering__PartitionDesc_IncludeInstrNode, 
  (void*)ValueNumbering__PartitionDesc_ExcludeInstrNode, 
  (void*)ValueNumbering__PartitionDesc_Size, 
  (void*)ValueNumbering__PartitionDesc_GetAnyInstruction, 
  (void*)ValueNumbering__PartitionDesc_IsEmpty, 
  (void*)ValueNumbering__PartitionDesc_CreateInstrList
}};
struct _TD ValueNumbering__PartitionDesc_td = {
  NULL,
  &Types__TypeDesc_td.td,
  {
    ValueNumbering__PartitionDesc_tdb.btypes,
    _tb1.tbprocs,
    (const unsigned char*)_n2.name,
    &ValueNumbering_md.md,
    0, 
    '0', '1',
    sizeof(ValueNumbering__PartitionDesc),
    &ValueNumbering__InstrListDesc_td.td
  }
};

static const struct {
  int length;
  void* pad;
  const char name[14];
} _n3 = {14, NULL, {"InstrNodeDesc"}};
static const struct {
  int length;
  void* pad;
  _Type btypes[2];
} ValueNumbering__InstrNodeDesc_tdb = {
  2, 
  NULL, 
  {
    &Data__InfoDesc_td.td, 
    &ValueNumbering__InstrNodeDesc_td.td
  }
};
static const struct {
  int length;
  void* pad;
  const void* tbprocs[1];
} _tb2 = {0, NULL, {
  NULL
}};
struct _TD ValueNumbering__InstrNodeDesc_td = {
  NULL,
  &Types__TypeDesc_td.td,
  {
    ValueNumbering__InstrNodeDesc_tdb.btypes,
    _tb2.tbprocs,
    (const unsigned char*)_n3.name,
    &ValueNumbering_md.md,
    1, 
    '0', '1',
    sizeof(ValueNumbering__InstrNodeDesc),
    &ValueNumbering__PartitionDesc_td.td
  }
};

/* local strings */

