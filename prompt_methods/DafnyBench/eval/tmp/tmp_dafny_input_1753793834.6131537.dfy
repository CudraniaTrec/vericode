
method max(a: array<int>, b: array<int>, i: int, j: int)
  returns (m: int)
  requires 0 <= i < a.Length
  requires 0 <= j < b.Length
  ensures  a[i] > b[j] ==> m == a[i]
  ensures  a[i] <= b[j] ==> m == b[j]
{
  // Strongest possible: assert the preconditions
  assert 0 <= i < a.Length;
  assert 0 <= j < b.Length;
  if a[i] > b[j] {
    m := a[i];
    assert m == a[i];
    assert a[i] > b[j];
    assert a[i] > b[j] ==> m == a[i];
  } else  {
    m := b[j];
    assert m == b[j];
    assert a[i] <= b[j];
    assert a[i] <= b[j] ==> m == b[j];
  }
  // Postcondition coverage
  assert (a[i] > b[j] ==> m == a[i]) && (a[i] <= b[j] ==> m == b[j]);
}

method testMax(a:array<int>, b:array<int>, i: int, j: int)
  requires 0 <= i < a.Length
  requires 0 <= j < b.Length
{
  // Precondition assertions
  assert 0 <= i < a.Length;
  assert 0 <= j < b.Length;
  var max := max(a,b,i,j);
  // Postcondition assertions
  assert a[i] > b[j] ==> max == a[i];
  assert a[i] <= b[j] ==> max == b[j];
}

function abs(a: real) : real {if a>0.0 then a else -a}
