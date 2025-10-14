method PairwiseAddition(seq: seq<int>) returns (result: seq<int>)
  ensures |result| == if |seq| < 2 then 0 else |seq| - 1
  ensures forall i :: 0 <= i < |result| ==> result[i] == seq[i] + seq[i+1]
{
  if |seq| < 2 {
    result := [];
  } else {
    var temp := new int[|seq| - 1];
    var i := 0;
    while i < |seq| - 1
      invariant 0 <= i <= |seq| - 1
      invariant forall j :: 0 <= j < i ==> temp[j] == seq[j] + seq[j+1]
    {
      temp[i] := seq[i] + seq[i+1];
      i := i + 1;
    }
    result := temp[..];
  }
}