method append(a:array<int>, b:int) returns (c:array<int>)
  ensures  a[..] + [b] == c[..]
{
  c := new int[a.Length+1];
  var i:= 0;
  while (i < a.Length)
    invariant 0 <= i <= a.Length
    invariant c.Length == a.Length + 1
    invariant forall j :: 0 <= j < i ==> c[j] == a[j]
  {
    c[i] := a[i];
    i:=i+1;
  }
  c[a.Length]:=b;
  assert forall j :: 0 <= j < a.Length ==> c[j] == a[j];
  assert c[a.Length] == b;
  assert c[..] == a[..] + [b];
}
function abs(a: real) : real {if a>0.0 then a else -a}
