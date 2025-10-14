method ElementwiseSum(a: seq<int>, b: seq<int>) returns (c: seq<int>)
  requires |a| == |b|
  ensures |c| == |a|
  ensures forall i :: 0 <= i < |a| ==> c[i] == a[i] + b[i]
{
  var result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == a[j] + b[j]
  {
    result := result + [a[i] + b[i]];
    i := i + 1;
  }
  c := result;
}