
function Potencia(x:nat, y:nat):nat
{
    if y == 0
    then 1
    else x * Potencia(x, y-1)
}

method Pot(x:nat, y:nat) returns (r:nat)
ensures r == Potencia(x,y)
{
    r := 1;
    var b := x;
    var e := y;
    while e > 0
        invariant 0 <= e <= y
        invariant r * b^e == x^y
        invariant b == x
    {
        r := r * b;
        e := e - 1;
        assert r * b^e == x^y;
    }

    assert r == x^y;
    return r;
}

function abs(a: real) : real {if a>0.0 then a else -a}
