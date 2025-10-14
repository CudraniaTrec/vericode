function to_seq<T>(a: array<T>, i: int) : (res: seq<T>)
requires 0 <= i <= a.Length
ensures res == a[i..]
reads a
decreases a.Length - i
{
  if i == a.Length
  then []
  else [a[i]] + to_seq(a, i + 1)
}

method Main() {
  var a: array<int> := new int[2];
  a[0] := 2;
  a[1] := 3;

  var ms: multiset<int> := multiset(a[..]);
}

function abs(a: real) : real {if a>0.0 then a else -a}
