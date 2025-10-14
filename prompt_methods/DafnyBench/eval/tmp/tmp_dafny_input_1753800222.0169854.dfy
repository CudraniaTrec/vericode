
// RUN: /print:log.bpl

method ArrayMap<A>(f: int -> A, a: array<A>)
  requires a != null
  requires forall j :: 0 <= j < a.Length ==> f.requires(j)
  requires forall j :: 0 <= j < a.Length ==> a !in f.reads(j)
  modifies a
  ensures forall j :: 0 <= j < a.Length ==> a[j] == f(j)
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] == f(j)
    invariant forall j :: i <= j < a.Length ==> true
  {
    a[i] := f(i);
    assert a[i] == f(i);
    i := i + 1;
  }
}


/*method GenericSort<A>(cmp: (A, A) -> bool, a: array<A>)
  requires a != null
  requires forall x, y :: a !in cmp.reads(x, y)
  requires forall x, y :: cmp.requires(x, y)
  modifies a
  ensures forall x, y :: cmp.requires(x, y)
  ensures forall x, y :: 0 <= x < y < a.Length ==> cmp(a[x], a[y])
{

  var i := 0;

  while i < a.Length
    modifies a
    invariant 0 <= i <= a.Length
    invariant forall x, y :: 0 <= x < y < i ==> cmp(a[x], a[y])
  {
    var j := i - 1;
    while j >= 0 && !cmp(a[j], a[i])
      modifies a
      invariant -1 <= j < i
      invariant forall k :: 0 <= k < j ==> cmp(a[k], a[k+1])
      invariant forall k :: j+1 <= k < i ==> cmp(a[k], a[k+1])
    {
      a[i], a[j] := a[j], a[i];
      j := j - 1;
    }

    i := i + 1;
  }

}*/

function abs(a: real) : real {if a>0.0 then a else -a}
