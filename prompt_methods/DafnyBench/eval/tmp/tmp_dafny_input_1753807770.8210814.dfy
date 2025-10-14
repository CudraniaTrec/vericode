
// Ex 1.3
method Triple (x: int) returns (r: int)
  ensures r == 3*x {
  var y := 2*x;
  assert y == 2*x;
  r := y + x;
  assert r == 2*x + x;
  assert r == 3*x;
}

method Caller() {
  var t := Triple(18);
  assert t == 54;
}

// Ex 1.6
method MinUnderSpec (x: int, y: int) returns (r: int)
  ensures r <= x && r <= y {
  if x <= y {
    assert x <= y;
    r := x - 1;
    assert r == x - 1;
    assert r < x;
    assert r <= y;
  } else {
    assert x > y;
    r := y - 1;
    assert r == y - 1;
    assert r < y;
    assert r <= x;
  }
  assert r <= x && r <= y;
}

method Min (x: int, y: int) returns (r: int)
  ensures r <= x && r <= y
  ensures r == x || r == y {
  if x <= y {
    assert x <= y;
    r := x;
    assert r == x;
    assert r <= x && r <= y;
    assert r == x || r == y;
  } else {
    assert x > y;
    r := y;
    assert r == y;
    assert r <= x && r <= y;
    assert r == x || r == y;
  }
  assert r <= x && r <= y;
  assert r == x || r == y;
}

// Ex 1.7
method MaxSum (x: int, y: int) returns (s:int, m: int)
  ensures s == x + y
  ensures x <= m && y <= m
  ensures m == x || m == y
// look ma, no implementation!

method MaxSumCaller() {
  var s, m := MaxSum(1928, 1);
  assert s == 1928 + 1;
  assert m == 1928 || m == 1;
  assert 1928 <= m && 1 <= m;
}

// Ex 1.8
method ReconstructFromMaxSum (s: int, m: int ) returns (x: int, y: int)
  // requires (0 < s && s / 2 < m && m < s)
  requires s - m <= m
  ensures s == x + y
  ensures (m == y || m == x) && x <= m && y <= m
{
  x := m;
  y := s - m;
  assert x == m;
  assert y == s - m;
  assert x + y == m + (s - m) == s;
  assert s == x + y;
  assert x == m || y == m;
  assert x <= m;
  assert y <= m;
}

// The following assertion holds if the commented-out requires are assumed in TestMaxSum
method TestMaxSum(x: int, y: int)
  // requires x > 0 && y > 0 && x != y
{
  var s, m := MaxSum(x, y);
  assert s == x + y;
  assert m == x || m == y;
  assert x <= m && y <= m;
  var xx, yy := ReconstructFromMaxSum(s, m);
  assert xx + yy == s;
  assert (m == xx || m == yy) && xx <= m && yy <= m;
}

// Ex 1.9
function Average (a: int, b: int): int {
  (a + b) / 2
}

method Triple'(x: int) returns (r: int)
  // spec 1: ensures Average(r, 3*x) == 3*x
  ensures Average(2*r, 6*x) == 6*x
{
  // r := x + x + x + 1;  // does not meet spec of Triple, but does spec 1
  r := x + x + x;
  assert r == 3*x;
  assert 2*r == 6*x;
  assert Average(2*r, 6*x) == (2*r + 6*x) / 2;
  assert (2*r + 6*x) / 2 == (6*x + 6*x)/2 == 12*x/2 == 6*x;
}

function abs(a: real) : real {if a>0.0 then a else -a}
