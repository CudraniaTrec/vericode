// Dafny Code

method ElementwiseAndSeq(a: seq<bool>, b: seq<bool>) returns (res: seq<bool>)
  requires |a| == |b|
  ensures |res| == |a|
  ensures forall i :: 0 <= i < |a| ==> res[i] == a[i] && b[i]
{
  res := seq i := 0 to |a| - 1 :: a[i] && b[i];
}