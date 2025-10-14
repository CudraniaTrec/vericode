
ghost function sum(n: nat): int
{
    if n == 0 then 0 else n + sum(n - 1)
}

method Sum(n: nat) returns (s: int)
ensures s == sum(n)
{

    var x:nat := 0;
    var y:nat := 1;
    var k:nat := n;
    while k > 0
        invariant 0 <= k <= n
        invariant x == sum(n) - sum(k)
        invariant y == 1
    {
        x := x + y*k;
        assert x == sum(n) - sum(k) + k; // after update
        k := k-1;
    }
    assert k == 0;
    assert x == sum(n) - sum(0);
    s := x;

}

function abs(a: real) : real {if a>0.0 then a else -a}
