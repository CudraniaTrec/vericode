method Max(a: int, b:int) returns (c: int)
    ensures c >= a && c>= b
{
    if (a < b)
        { 
            // In this branch, b > a, so b >= a and b >= b
            c := b; 
        }
    else
        { 
            // In this branch, a >= b, so a >= a and a >= b
            c := a; 
        }
    // After the if-else, c is either a or b, and in both cases c >= a && c >= b
    assert c >= a && c >= b;
}   

method Testing()
{
    var v := Max(2, 3);
    assert v == 3;
    assert v >= 2 && v >= 3;
}

function abs(a: real) : real {if a>0.0 then a else -a}
