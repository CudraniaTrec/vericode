method minArray(a: array<int>) returns (r:int)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> r <= a[i]
  ensures exists i :: 0 <= i < a.Length && r == a[i]
{
  r:=a[0];
  var i:=1;
  while i<a.Length
    invariant 1 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> r <= a[j]
    invariant exists j :: 0 <= j < i && r == a[j]
    invariant r == min(a[..i])
  {
    if r>a[i]{
      r:=a[i];
    }
    i:=i+1;
  }
  assert forall j :: 0 <= j < a.Length ==> r <= a[j];
  assert exists j :: 0 <= j < a.Length && r == a[j];
}
function abs(a: real) : real {if a>0.0 then a else -a}
