method BigFoot(step: nat) // DO NOT CHANGE
requires 0 < step <= 42;
{
    var indx := 0; // DO NOT CHANGE
    while indx<=42 // DO NOT CHANGE
        invariant 0 <= indx <= 42;
        invariant indx % step == 0;
    { indx := indx+step; } // DO NOT CHANGE
}
function abs(a: real) : real {if a>0.0 then a else -a}
