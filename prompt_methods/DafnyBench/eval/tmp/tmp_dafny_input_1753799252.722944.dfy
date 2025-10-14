
function Potencia(x: nat, y: nat): nat
{
    if y == 0
    then 1
    else x * Potencia(x, y-1) 
}

method Pot(x: nat, y: nat) returns (r: nat)
ensures r == Potencia(x,y)
{
    var b := x;
    var e := y;
    r := 1;

    while e > 0
        invariant 0 <= e <= y
        invariant r * Potencia(b, e) == Potencia(x, y)
    {
        r := b * r;
        e := e - 1;
        assert r * Potencia(b, e) == Potencia(x, y);
    }

    assert e == 0;
    assert r * Potencia(b, e) == Potencia(x, y);
    assert Potencia(b, 0) == 1;
    assert r == Potencia(x, y);
    return r;
}

function abs(a: real) : real {if a>0.0 then a else -a}
