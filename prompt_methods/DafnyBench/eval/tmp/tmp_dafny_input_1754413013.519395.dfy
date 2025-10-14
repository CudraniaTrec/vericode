
//Problem01
//a)
ghost function gcd(x: int, y: int): int
    requires x > 0 && y > 0
{
    if x == y then x
    else if x > y then gcd(x - y, y)
    else gcd(x, y - x)
}

method gcdI(m: int, n: int) returns (d: int)
requires  m > 0 && n > 0 
ensures d == gcd(m, n);
{
    var x: int;
    d := m;
    x := n;
    while (d != x)
        invariant d > 0 && x > 0
        invariant gcd(d, x) == gcd(m, n)
        invariant d <= m && x <= n
    {
        if (d > x)
        {
            d := d - x;
            assert d > 0;
        }
        else
        {
            x := x - d;
            assert x > 0;
        }
    }
    assert d == x;
    assert d == gcd(m, n);
}

//b)
ghost function gcd'(x: int, y: int): int
    requires x > 0 && y > 0
{
    if x == y then x
    else if x > y then gcd'(x - y, y)
    else gcd(y, x)
}

function abs(a: real) : real {if a>0.0 then a else -a}
