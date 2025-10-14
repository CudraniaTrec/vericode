
method max(a: array<int>, b: array<int>, i: int, j: int)
  returns (m: int)
  requires 0 <= i < a.Length
  requires 0 <= j < b.Length
  ensures  a[i] > b[j] ==> m == a[i]
  ensures  a[i] <= b[j] ==> m == b[j]
{
  if a[i] > b[j] {
    m := a[i];
    assert m == a[i];
    assert a[i] > b[j];
    assert a[i] > b[j] ==> m == a[i];
    assert a[i] <= b[j] ==> m == b[j];
  } else  {
    m := b[j];
    assert m == b[j];
    assert a[i] <= b[j];
    assert a[i] > b[j] ==> m == a[i];
    assert a[i] <= b[j] ==> m == b[j];
  }
  assert (a[i] > b[j] ==> m == a[i]) && (a[i] <= b[j] ==> m == b[j]);
}

method testMax(a:array<int>, b:array<int>, i: int, j: int)
  requires 0 <= i < a.Length
  requires 0 <= j < b.Length
{
  var max := max(a,b,i,j);
  assert max == (if a[i] > b[j] then a[i] else b[j]);
}

function abs(a: real) : real {if a>0.0 then a else -a}
