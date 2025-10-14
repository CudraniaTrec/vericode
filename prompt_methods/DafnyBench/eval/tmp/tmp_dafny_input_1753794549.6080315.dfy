
method Index(n: int) returns (i: int) 
requires 1 <= n
ensures 0 <= i < n
{
    // n >= 1
    i := n/2;
    assert 0 <= i;
    assert i < n;
}

method Min(x: int, y: int) returns (m: int) 
ensures m <= x && m <= y
ensures m == x || m == y
{
    if (x >= y) {
        m := y;
        assert m <= x && m <= y;
        assert m == x || m == y;
    } else {
        m := x;
        assert m <= x && m <= y;
        assert m == x || m == y;
    }
}

method Max(x: int, y: int) returns (m: int) {
    if (x >= y) {
        m := x;
        assert m >= y;
        assert m == x || m == y;
    } else {
        m := y;
        assert m >= x;
        assert m == x || m == y;
    }
}

method MaxSum(x: int, y: int) returns (s: int, m: int)
  ensures s == x + y
  ensures m == if x >= y then x else y
{
    s := x + y;
    assert s == x + y;
    if (x >= y) {
        m := x;
        assert m == (if x >= y then x else y);
    } else {
        m := y;
        assert m == (if x >= y then x else y);
    }
}

method MaxSumCaller() {
    var x: int := 1928;
    var y: int := 1;
    var a, b: int;
    a, b := MaxSum(x, y);
    assert a == x + y;
    assert b == if x >= y then x else y;
}

method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int)
    requires s <= 2 * m
    ensures s == (x + y)
    ensures (m == x || m == y) && x <= m && y <= m
{
    x := m;
    y := s - m;
    assert s == x + y;
    assert (m == x || m == y);
    assert x <= m && y <= m;
}

method TestMaxSum(x: int, y: int) 
{
    var s, m := MaxSum(x, y);
    assert s == x + y;
    assert m == (if x >= y then x else y);
    var xx, yy := ReconstructFromMaxSum(s, m);
    assert s == xx + yy;
    assert (m == xx || m == yy) && xx <= m && yy <= m;
}

function abs(a: real) : real {if a>0.0 then a else -a}
