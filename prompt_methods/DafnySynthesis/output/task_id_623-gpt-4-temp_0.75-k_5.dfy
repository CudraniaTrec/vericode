method PowList(l: seq<int>, n: nat) returns (res: seq<int>)
  ensures res == l.Map(x => x ^ n)
{
  var r := new int[l.Length];
  var i := 0;
  while i < l.Length
    invariant 0 <= i <= l.Length
    invariant r[..i] == l[..i].Map(x => x ^ n)
  {
    r[i] := l[i] ^ n;
    i := i + 1;
  }
  res := r[..];
}