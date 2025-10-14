method ClosestSmaller(n: int) returns (m: int)
    requires n > 0
    ensures m + 1 == n
{
    assert n > 0;
    m := n - 1;
    assert m + 1 == n;
}
function abs(a: real) : real {if a>0.0 then a else -a}
