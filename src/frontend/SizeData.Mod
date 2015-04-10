MODULE SizeData;

IMPORT
  D := Data, Out;
  
PROCEDURE WriteSize (name: ARRAY OF CHAR; size: LONGINT);
  BEGIN
    Out.String (name);
    Out.String (": ");
    Out.Int (size, 0);
    Out.String (" bytes");
    Out.Ln
  END WriteSize;

BEGIN
  WriteSize ("InfoDesc", SIZE (D.InfoDesc));
  WriteSize ("NodeDesc", SIZE (D.NodeDesc));
  WriteSize ("UsableDesc", SIZE (D.UsableDesc));
  WriteSize ("OpndDesc", SIZE (D.OpndDesc));
  WriteSize ("ConstDesc", SIZE (D.ConstDesc));
  WriteSize ("ResultDesc", SIZE (D.ResultDesc));
  WriteSize ("AddressableDesc", SIZE (D.AddressableDesc));
  WriteSize ("ObjectDesc", SIZE (D.ObjectDesc));
  WriteSize ("StructDesc", SIZE (D.StructDesc));
  WriteSize ("InstructionDesc", SIZE (D.InstructionDesc));
  WriteSize ("RegionDesc", SIZE (D.RegionDesc));
  WriteSize ("GateDesc", SIZE (D.GateDesc));
  WriteSize ("GuardDesc", SIZE (D.GuardDesc));
  WriteSize ("MergeDesc", SIZE (D.MergeDesc))
END SizeData.
