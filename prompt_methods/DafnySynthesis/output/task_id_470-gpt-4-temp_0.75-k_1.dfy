method addPairwise(n: seq<int>) returns (res: seq<int>)
  ensures |res| == if |n| >= 2 then |n| - 1 else 0
  ensures forall i :: 0 <= i < |res| ==> res[i] == n[i] + n[i+1]
{
  if |n| < 2 {
    res := [];
    return;
  }
  var tmp := new int[|n|-1];
  var i := 0;
  while i < |n|-1
    invariant 0 <= i <= |n|-1
    invariant forall j :: 0 <= j < i ==> tmp[j] == n[j] + n[j+1]
  {
    tmp[i] := n[i] + n[i+1];
    i := i + 1;
  }
  res := tmp[..];
}