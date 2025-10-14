method CountToAndReturnN(n: int) returns (r: int)
    requires n >= 0
    ensures r == n 
{
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant r == 0
    {
        i := i + 1;
        assert i <= n;
    }
    r := i;
    assert r == n;
}
function abs(a: real) : real {if a>0.0 then a else -a}
