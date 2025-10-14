
method div_ent_it(a: int, b: int) returns (c: int, r: int)

// Algoritmo iterativo de la división de enteros
// que calcula su cociente y resto

    requires a >= 0 && b > 0
    ensures  a == b*c + r && 0 <= r < b
{
    c := 0; r := a ;
    while (r >= b)
        invariant 0 <= c <= a
        invariant r >= 0
        invariant a == b*c + r
        invariant b > 0
        decreases r
    {
        c := c + 1 ;
        r := r - b ;
        assert a == b*c + r;
        assert r >= 0;
    }
    assert 0 <= r < b;
    assert a == b*c + r;
}

method Main()
{
    var c, r := div_ent_it(6 , 2) ;
    print "Cociente: ", c, ", Resto: ", r ;
}

function abs(a: real) : real {if a>0.0 then a else -a}
