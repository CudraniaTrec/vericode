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
        invariant x + y == a + b
        invariant x >= y
        invariant x >= b
        invariant y <= a
        invariant a >= b
        invariant Par(a-b)
    {
        x := x - 1;
        y := y + 1;
    }
}
function abs(a: real) : real {if a>0.0 then a else -a}
