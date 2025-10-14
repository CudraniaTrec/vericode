method InsertBeforeEach(xs: seq<string>, s: string) returns (res: seq<string>)
  ensures |res| == 2 * |xs|
  ensures forall i :: 0 <= i < |xs| ==> res[2*i] == s && res[2*i + 1] == xs[i]
{
  var acc := [];
  var i := 0;
  while i < |xs|
    invariant 0 <= i <= |xs|
    invariant |acc| == 2 * i
    invariant forall j :: 0 <= j < i ==> acc[2*j] == s && acc[2*j + 1] == xs[j]
  {
    acc := acc + [s, xs[i]];
    i := i + 1;
  }
  res := acc;
}