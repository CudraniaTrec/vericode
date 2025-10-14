method Mult(x:nat, y:nat) returns (r: nat)
ensures r == x * y
{
    var m := x;
    var n := y;
    r:=0;

    while m > 0
        invariant 0 <= m <= x
        invariant n == y
        invariant r == (x - m) * y
    {
        r := r + n;
        m := m - 1;
        assert r == (x - m) * y - y + n;
    }

    return r;
}
function abs(a: real) : real {if a>0.0 then a else -a}
