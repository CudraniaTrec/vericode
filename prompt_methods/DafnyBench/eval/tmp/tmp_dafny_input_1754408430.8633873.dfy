
method main(n: int) returns(x: int, m: int)
requires n > 0
ensures (n <= 0) || (0 <= m && m < n)
{
    x := 0;
    m := 0;

    while(x < n)
        invariant 0 <= x <= n
        invariant 0 <= m <= x
    {
        if(*)
        {
            m := x;
            assert 0 <= m <= x;
        }
        else{}
        x := x + 1;
    }
    assert 0 <= m <= x;
    assert x == n;
    assert 0 <= m && m < n;
}

function abs(a: real) : real {if a>0.0 then a else -a}
