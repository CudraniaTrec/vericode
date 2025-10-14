//Dafny Code

method IndexWiseMultiply(s1: seq<int>, s2: seq<int>) returns (result: seq<int>)
  requires |s1| == |s2|
  ensures |result| == |s1|
  ensures forall i :: 0 <= i < |s1| ==> result[i] == s1[i] * s2[i]
{
  var temp := [];
  var i := 0;
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant temp == [s1[j] * s2[j] | j := 0 .. i]
  {
    temp := temp + [s1[i] * s2[i]];
    i := i + 1;
  }
  result := temp;
}