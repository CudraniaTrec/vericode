
method GenericMax<A>(cmp: (A, A) -> bool, a: array<A>) returns (max: A)
  requires a != null && a.Length > 0
  requires forall x, y :: cmp.requires(x, y)
  requires forall x, y :: cmp(x, y) || cmp(y, x);
  requires forall x, y, z :: cmp(x, y) && cmp(y, z) ==> cmp(x, z);

  ensures forall x :: 0 <= x < a.Length ==>
    // uncommenting the following line causes the program to verify
    // assume cmp.requires(a[x], max);
    cmp(a[x], max)
{
  max := a[0];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> cmp(a[j], max)
    invariant exists k :: 0 <= k < a.Length && max == a[k]
    invariant cmp.requires(a[i-1 < 0 ? 0 : i-1], max)
  {
    if !cmp(a[i], max) {
      max := a[i];
      assert exists k :: 0 <= k <= i && max == a[k];
    }
    i := i + 1;
  }
  assert forall x :: 0 <= x < a.Length ==> cmp(a[x], max);
}

function abs(a: real) : real {if a>0.0 then a else -a}
