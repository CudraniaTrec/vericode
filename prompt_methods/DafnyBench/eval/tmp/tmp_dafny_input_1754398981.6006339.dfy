method arrayProduct(a: array<int>, b: array<int>) returns (c: array<int> )
  requires a.Length==b.Length
  ensures c.Length==a.Length
  ensures forall i:: 0 <= i< a.Length==> a[i] * b[i]==c[i]
{
  c:= new int[a.Length];
  var i:=0;
  while i<a.Length
    invariant 0 <= i <= a.Length
    invariant c.Length == a.Length
    invariant forall j :: 0 <= j < i ==> c[j] == a[j] * b[j]
    invariant a.Length == b.Length
  {
    c[i]:=a[i]*b[i];
    i:=i+1;
  }
  assert c.Length == a.Length;
  assert forall i :: 0 <= i < a.Length ==> c[i] == a[i] * b[i];
}
function abs(a: real) : real {if a>0.0 then a else -a}
