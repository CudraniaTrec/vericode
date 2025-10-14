predicate Par(n:int)
{
    n % 2 == 0
}

method FazAlgo (a:int, b:int) returns (x:int, y:int)
requires a >= b && Par (a-b)
{
    x := a;
    y := b;
    while x != y
        invariant a >= b
        invariant Par(a - b)
        invariant x + y == a + b
        invariant x >= y
        invariant Par(x - y)
        invariant (x - y) % 2 == 0
        invariant x >= y
        decreases x - y
    {
        x := x - 1;
        y := y + 1;
        assert x + y == a + b;
        assert x >= y;
        assert Par(x - y);
    }
    assert x == y;
    assert x + y == a + b;
    assert Par(a - b);
}

function abs(a: real) : real {if a>0.0 then a else -a}
