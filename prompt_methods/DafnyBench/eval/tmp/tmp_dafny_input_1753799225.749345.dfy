
method Carre(a: nat) returns (c: nat)
ensures c == a*a
{
    var i := 0;
    c := 0;
    while i != a
        invariant 0 <= i <= a
        invariant c == i * i
    {
        c := c + 2*i +1;
        i := i + 1;
    }
    assert c == a*a;
}

function abs(a: real) : real {if a>0.0 then a else -a}
