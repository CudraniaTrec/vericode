
method main(n: int, k: int) returns (k_out: int)
    requires n > 0;
    requires k > n;
    ensures k_out >= 0;
{
    k_out := k;
    var j: int := 0;
    while(j < n)
        invariant 0 <= j <= n
        invariant k_out == k - j
        invariant k_out >= k - n
        invariant k_out >= 0
    {
        j := j + 1;
        k_out := k_out - 1;
        assert k_out == k - j;
        assert k_out >= k - n;
        assert k_out >= 0;
    }
    assert k_out == k - n;
    assert k_out >= 0;
}

function abs(a: real) : real {if a>0.0 then a else -a}
