method main(n: int) returns (a: int, b: int)
    requires n >= 0
    ensures a + b == 3 * n
{
    var i: int := 0;
    a := 0;
    b := 0;

    while(i < n)
        invariant 0 <= i <= n
        invariant a + b == 3 * i
    {
        if(*)
        {
            a := a + 1;
            b := b + 2;
        }
        else
        {
            a := a + 2;
            b := b + 1;
        }

        i := i + 1;
        assert a + b == 3 * i;
    }
    assert a + b == 3 * n;
}

function abs(a: real) : real {if a>0.0 then a else -a}
