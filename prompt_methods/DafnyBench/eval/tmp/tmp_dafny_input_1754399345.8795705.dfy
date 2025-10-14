method Match(s: string, p: string) returns (b: bool)
  requires |s| == |p|
  ensures b <==> forall n :: 0 <= n < |s| ==> s[n] == p[n] || p[n] == '?'
{
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall n :: 0 <= n < i ==> s[n] == p[n] || p[n] == '?'
  {
    if s[i] != p[i] && p[i] != '?'
    {
      assert !(s[i] == p[i] || p[i] == '?');
      return false;
    }
    assert s[i] == p[i] || p[i] == '?';
    i := i + 1;
  }
  assert forall n :: 0 <= n < |s| ==> s[n] == p[n] || p[n] == '?';
  return true;
}
function abs(a: real) : real {if a>0.0 then a else -a}
