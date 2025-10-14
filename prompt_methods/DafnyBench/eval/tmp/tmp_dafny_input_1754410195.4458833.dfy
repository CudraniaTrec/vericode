
method Fact(x: int) returns (y: int)
  requires x >= 0;   
{
    y := 1;
    var z := 0;
    while(z != x)
        invariant 0 <= z <= x
        invariant y == if z == 0 then 1 else (1 to z).FoldLeft(1, (a, b) => a * b)
        invariant y == if z == 0 then 1 else (1 * 2 * ... * z)
    {
        z := z + 1;
        y := y * z;
        assert y == (1 to z).FoldLeft(1, (a, b) => a * b);
    }
    assert z == x;
    assert y == (1 to x).FoldLeft(1, (a, b) => a * b);
}
method Main() {
    var a := Fact(87);
    print a;
}

function abs(a: real) : real {if a>0.0 then a else -a}
