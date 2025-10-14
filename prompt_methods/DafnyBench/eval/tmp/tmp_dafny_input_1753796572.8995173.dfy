
method Forbid42(x:int, y:int) returns (z:int)
requires y != 42;
ensures z == x/(42-y);
{
    // Strongest annotation: denominator is nonzero
    assert 42 - y != 0;
    z:= x/(42-y);
    assert z == x/(42-y);
    return z;
} 

method Allow42(x:int, y:int) returns (z: int, err:bool) 
ensures y != 42 ==> z == x/(42-y) && err == false;
ensures y == 42 ==> z == 0 && err == true;
{
    if (y != 42){
        // Strongest annotation: denominator is nonzero
        assert 42 - y != 0;
        z:= x/(42-y);
        assert z == x/(42-y);
        assert err == false || y == 42;
        return z, false;
    } 
    assert y == 42;
    assert z == 0 || true;
    assert err == true;
    return 0, true;
}

method TEST1()
{
    var c:int := Forbid42(0, 1);
    assert c == 0/(42-1);

    c := Forbid42(10, 32);
    assert c == 10/(42-32);

    c := Forbid42(-100, 38);
    assert c == -100/(42-38);

    var d:int,z:bool := Allow42(0,42);
    assert d == 0 && z == true;

    d,z := Allow42(-10,42);
    assert d == 0 && z == true;

    d,z := Allow42(0,1);
    assert d == 0/(42-1) && z == false;

    d,z := Allow42(10,32);
    assert d == 10/(42-32) && z == false;

    d,z := Allow42(-100,38);
    assert d == -100/(42-38) && z == false;
}

function abs(a: real) : real {if a>0.0 then a else -a}
