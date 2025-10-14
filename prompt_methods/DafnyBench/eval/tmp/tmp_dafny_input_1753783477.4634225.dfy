method only_once<T(==)>(a: array<T>, key: T) returns (b:bool)
  ensures (multiset(a[..])[key] ==1 ) <==> b
{
  var i := 0;
  b := false;
  var keyCount := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant keyCount == multiset(a[..i])[key]
    invariant b == (keyCount == 1)
  {
    if (a[i] == key)
    {
      keyCount := keyCount + 1;
    }
    if (keyCount == 1)
    { b := true; }
    else
    { b := false; }
    i := i + 1;
  }
  // At this point, i == a.Length, so keyCount == multiset(a[..])[key]
  // and b == (keyCount == 1)
}

function abs(a: real) : real {if a>0.0 then a else -a}
