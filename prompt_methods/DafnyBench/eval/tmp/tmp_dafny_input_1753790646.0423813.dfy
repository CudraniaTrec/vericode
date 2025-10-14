method Max(a: int, b:int) returns (c: int)
    ensures c >= a && c>= b
{
    if (a < b)
        { 
            c := b; 
        }
    else
        { 
            c := a; 
        }
    // assert c >= a && c >= b; // follows from the logic above and is ensured by the postcondition
}   

method Testing()
{
    var v := Max(2, 3);
    // assert v == 3; // cannot be proven from the contract alone
    assert v >= 2 && v >= 3;
}

function abs(a: real) : real {if a>0.0 then a else -a}
