method TetrahedralNumber(n: int) returns (t: int)
    requires n >= 0
    ensures t == n * (n + 1) * (n + 2) / 6
{
    assert n >= 0;
    t := n * (n + 1) * (n + 2) / 6;
    assert t == n * (n + 1) * (n + 2) / 6;
}
function abs(a: real) : real {if a>0.0 then a else -a}
