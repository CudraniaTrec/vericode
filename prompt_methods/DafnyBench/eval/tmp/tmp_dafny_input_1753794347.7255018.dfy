
method main() returns (t1: int, t2: int, x: int, y: int)
ensures y >= 1
{
    x := 1;
    y := 1;
    t1 := 0;
    t2 := 0;

    while(x <= 100000) 
        invariant x >= 1
        invariant y >= 1
        invariant t1 >= 1 || x == 1
        invariant t2 >= 1 || y == 1
        invariant x == y
    {
        t1 := x;
        t2 := y;
        x := t1 + t2;
        y := t1 + t2;
        assert x >= 1;
        assert y >= 1;
        assert x == y;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
