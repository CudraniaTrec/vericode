
method Two(x: int) returns (y: int)
ensures y == x + 1
{
    var a:= x+1;
    assert a == x + 1;
    if(a - 1 == 0){
        // a - 1 == 0 ==> a == 1 ==> x + 1 == 1 ==> x == 0
        assert x == 0;
        y:= 1;
        assert y == x + 1;
    } else {
        // a - 1 != 0 ==> a != 1 ==> x + 1 != 1 ==> x != 0
        assert x != 0;
        y:= a;
        assert y == x + 1;
    }
    assert y == x + 1;
}

function abs(a: real) : real {if a>0.0 then a else -a}
