
method remove_front(a:array<int>) returns (c:array<int>)
  requires a.Length>0
  ensures  a[1..] == c[..]
{
  c := new int[a.Length-1];
  var i:= 1;
  while (i < a.Length)
    invariant 1 <= i <= a.Length
    invariant forall j :: 0 <= j < i-1 ==> c[j] == a[j+1]
    invariant c.Length == a.Length-1
  {
    c[i-1] := a[i];
    i:=i+1;
  }
  assert forall j :: 0 <= j < c.Length ==> c[j] == a[j+1];
}

function abs(a: real) : real {if a>0.0 then a else -a}
