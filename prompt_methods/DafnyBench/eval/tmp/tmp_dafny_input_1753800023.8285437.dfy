
// problem 2:
// name:      Gabriele Berardi
// s-number: s4878728
// table:     XXX

method problem2(p:int, q:int, X:int, Y:int) returns (r:int, s:int)
requires p == 2*X + Y && q == X + 3
ensures r == X && s == Y
{
    // p == 2*X + Y
    // q == X + 3

    r, s := p, q;
    // r == 2*X + Y
    // s == X + 3

    r := r - 2*s + 6;
    // r == (2*X + Y) - 2*(X + 3) + 6
    //   == 2*X + Y - 2*X - 6 + 6
    //   == Y
    // s == X + 3
    assert r == Y;
    assert s == X + 3;

    s := s - 3;
    // s == X + 3 - 3 == X
    assert s == X;
    assert r == Y;

    r,s := s, r;
    // r == X
    // s == Y
    assert r == X && s == Y;
}

function abs(a: real) : real {if a>0.0 then a else -a}
