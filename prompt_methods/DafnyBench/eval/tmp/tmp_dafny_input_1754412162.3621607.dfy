
predicate Par(n:int)
{
    n % 2 == 0
}

method FazAlgo (a:int, b:int) returns (x:int, y:int)
requires a >= b && Par (a-b)
ensures x == y && x + y == a + b && x >= b && y <= a && Par(a-b)
{
    x := a;
    y := b;
    while x != y
        invariant a >= b
        invariant Par(a-b)
        invariant x + y == a + b
        invariant x >= y
        invariant x >= b
        invariant y <= a
    {
        assert x > y;
        x := x - 1;
        y := y + 1;
    }
    assert x == y;
    assert x + y == a + b;
    assert x >= b;
    assert y <= a;
    assert Par(a-b);
}

function abs(a: real) : real {if a>0.0 then a else -a}
