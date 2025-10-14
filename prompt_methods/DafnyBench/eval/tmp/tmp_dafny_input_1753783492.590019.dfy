
method remove_front(a:array<int>) returns (c:array<int>)
  requires a.Length>0
  ensures  a[1..] == c[..]
{
  c := new int[a.Length-1];
  var i:= 1;
  while (i < a.Length)
    invariant 1 <= i <= a.Length
    invariant forall j :: 1 <= j < i ==> c[j-1] == a[j]
    invariant c.Length == a.Length - 1
  {
    c[i-1] := a[i];
    i:=i+1;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
