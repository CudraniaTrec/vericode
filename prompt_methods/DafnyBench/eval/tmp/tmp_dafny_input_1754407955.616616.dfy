method Abs(x:int) returns (y:int)
ensures y>=0;
ensures x>=0 ==> x == y;
ensures x<0 ==> -x == y;
ensures y == abs(x); // use this instead of line 3,4
{   
    if(x<0)
    {
        assert x < 0;
        y := -x;
        assert y >= 0;
        assert y == abs(x);
        return y;
    }
    else{
        assert x >= 0;
        y := x;
        assert y >= 0;
        assert y == abs(x);
        return y;
    }
}

// Renamed function to avoid duplicate name error
function abs(x: int): int
{
    if x >= 0 then x else -x
}

method Testing(){
    var v:= Abs(-3);
    assert v == 3;
    assert v >= 0;
    assert v == abs(-3);
}

method MultiReturn(x:int, y:int) returns (more:int, less:int)
requires y>=0;
ensures less <= x <= more;
{
    more := x + y;
    less := x - y;
    assert less <= x;
    assert x <= more;
}

method Max(x:int, y:int) returns (a:int)
ensures a == x || a == y;
ensures x > y ==> a == x;
ensures x <= y ==> a == y;
{
    if ( x > y ) 
    { 
        assert x > y;
        a := x;
        assert a == x;
    } else 
    { 
        assert x <= y;
        a := y; 
        assert a == y;
    }
    assert a == x || a == y;
    assert (x > y ==> a == x);
    assert (x <= y ==> a == y);
}

function abs(a: real) : real {if a>0.0 then a else -a}
