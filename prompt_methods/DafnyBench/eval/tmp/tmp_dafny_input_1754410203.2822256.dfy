
method Mult(x:nat, y:nat) returns (r:nat)
ensures r == x * y
{
    // Valores passados por parâmetros são imutáveis
    var m := x;
    var n := y;
    r := 0;
    // Soma sucessiva para multiplicar dois números.
    while m > 0
        invariant 0 <= m <= x
        invariant n == y
        invariant r + m * n == x * y
        invariant r >= 0
    {
        r := r + n;
        m := m - 1;
    }
    assert m == 0;
    assert r == x * y;
    return r; // NOT(m>0) ^ Inv ==> r = x*y
}

function abs(a: real) : real {if a>0.0 then a else -a}
