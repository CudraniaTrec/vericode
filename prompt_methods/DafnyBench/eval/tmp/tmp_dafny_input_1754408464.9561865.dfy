
function contains(v: int, a: array<int>, n: int): bool
reads a
  requires n <= a.Length
{
  exists j :: 0 <= j < n && a[j] == v
}

function upper_bound(v: int, a: array<int>, n: int): bool
reads a
  requires n <= a.Length
{
  forall j :: 0 <= j < n ==> a[j] <= v
}

function is_max(m: int, a: array<int>, n: int): bool
reads a
  requires n <= a.Length
{
  contains(m, a, n) && upper_bound(m, a, n)
}

method max(a: array<int>, n: int) returns (max: int)
  requires 0 < n <= a.Length;
  ensures is_max(max, a, n);
{
  var i: int := 1;

  max := a[0];

  while i < n
    invariant 1 <= n <= a.Length
    invariant 1 <= i <= n
    invariant contains(max, a, i)
    invariant upper_bound(max, a, i)
  {
    if a[i] > max {
      max := a[i];
      assert contains(max, a, i+1);
    }
    i := i + 1;
  }
  assert contains(max, a, n);
  assert upper_bound(max, a, n);
}

function abs(a: real) : real {if a>0.0 then a else -a}
