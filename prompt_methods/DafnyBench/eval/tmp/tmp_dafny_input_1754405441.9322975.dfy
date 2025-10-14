method Max(a: int, b:int) returns (c: int)
    ensures c >= a && c>= b
{
    // Both branches assign the greater of a and b to c.
    if (a < b)
        { 
            assert b >= a && b >= b;
            c := b; 
            assert c >= a && c >= b;
        }
    else
        { 
            assert a >= b && a >= a;
            c := a; 
            assert c >= a && c >= b;
        }
    assert c >= a && c >= b;
}   

method Testing()
{
    var v := Max(2, 3);
    assert v == 3;
    assert v >= 2 && v >= 3;
}

function abs(a: real) : real {if a>0.0 then a else -a}
