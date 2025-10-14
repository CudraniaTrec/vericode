method Mult(x:nat, y:nat) returns (r: nat)
ensures r == x * y
{
    var m := x;
    var n := y;
    r:=0;

    while m > 0
        invariant 0 <= m <= x
        invariant n == y
        invariant r + m * n == x * y
        invariant r >= 0
    {
        r := r + n;
        m := m - 1;
        assert r + m * n == x * y;
    }

    return r;
}
function abs(a: real) : real {if a>0.0 then a else -a}
