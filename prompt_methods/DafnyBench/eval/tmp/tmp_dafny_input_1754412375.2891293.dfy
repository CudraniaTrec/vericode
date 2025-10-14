function C(n: nat): nat 
{
    if n == 0 then 1 else (4 * n - 2) * C(n-1) / (n + 1) 
}

method calcC(n: nat) returns (res: nat)
    ensures res == C(n)
{
    var i := 0;
    res := 1;

    while i < n
        invariant 0 <= i <= n
        invariant res == C(i)
        decreases n - i
    {
        ghost var v0 := n - i;
        i := i + 1;
        // At this point, res == C(i-1)
        res := (4 * i - 2) * res / (i + 1);
        // Let's assert the step matches the function definition
        assert res == (4 * i - 2) * C(i-1) / (i + 1);
        assert res == C(i);
    }
    assert res == C(n);
}
function abs(a: real) : real {if a>0.0 then a else -a}
