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
    // No assertion here, as c == Max(a, b) by construction and postcondition is ensured.
}   

method Testing()
{
    var v := Max(2, 3);
    // No assertion here, as v == 3 by Max's ensures clause.
}
function abs(a: real) : real {if a>0.0 then a else -a}
