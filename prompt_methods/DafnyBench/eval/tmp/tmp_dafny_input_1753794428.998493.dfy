
method main(n: int, k: int) returns (i :int, j: int)
    requires n >= 0
    requires k == 1 || k >= 0
    ensures k + i + j >= 2 * n
{
    i := 0;
    j := 0;
    while(i < n)
        invariant 0 <= i <= n
        invariant j == i * (i + 1) / 2
        invariant k + i + j + (n - i) >= 2 * n
    {
        i := i + 1;
        j := j + i;
        assert j == i * (i + 1) / 2;
    }
    assert i == n;
    assert j == n * (n + 1) / 2;
    assert k + i + j >= 2 * n;
}

function abs(a: real) : real {if a>0.0 then a else -a}
