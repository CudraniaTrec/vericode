
method ArraySplit (a : array<int>) returns (b : array<int>, c : array<int>)
  ensures fresh(b)
  ensures fresh(c)
  ensures a[..] == b[..] + c[..]
  ensures a.Length == b.Length + c.Length
  ensures a.Length > 1 ==> a.Length > b.Length
  ensures a.Length > 1 ==> a.Length > c.Length
{
  var splitPoint : int := a.Length / 2;

  b := new int[splitPoint];
  c := new int[a.Length - splitPoint];

  var i : int := 0;

  while (i < splitPoint)
    invariant 0 <= i <= splitPoint
    invariant b[..i] == a[..i]
    invariant forall k :: i <= k < splitPoint ==> b[k] == 0
    invariant c[..0] == a[..0]
    invariant b.Length == splitPoint
    invariant c.Length == a.Length - splitPoint
  {
    b[i] := a[i];
    i := i + 1;
  }

  var j : int := 0;
  while (i < a.Length)
    invariant splitPoint <= i <= a.Length
    invariant 0 <= j <= c.Length
    invariant j == i - splitPoint
    invariant b[..] == a[..splitPoint]
    invariant c[..j] == a[splitPoint..i]
    invariant forall k :: j <= k < c.Length ==> c[k] == 0
    invariant b.Length == splitPoint
    invariant c.Length == a.Length - splitPoint
  {
    c[j] := a[i];
    i := i + 1;
    j := j + 1;
  }

  assert b[..] == a[..splitPoint];
  assert c[..] == a[splitPoint..a.Length];
  assert a[..] == b[..] + c[..];
  assert a.Length == b.Length + c.Length;
  assert b.Length == splitPoint;
  assert c.Length == a.Length - splitPoint;
  assert a.Length > 1 ==> a.Length > b.Length;
  assert a.Length > 1 ==> a.Length > c.Length;
}

function abs(a: real) : real {if a>0.0 then a else -a}
