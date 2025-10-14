
method BigFoot(step: nat) // DO NOT CHANGE
requires 0 < step <= 42;
{
    var indx := 0; // DO NOT CHANGE
    while indx<=42 // DO NOT CHANGE
        invariant 0 <= indx <= 42 + step;
        invariant indx % step == 0;
        invariant forall k :: 0 <= k < indx/step ==> 0 <= k*step <= 42;
    { indx := indx+step; } // DO NOT CHANGE
}

function abs(a: real) : real {if a>0.0 then a else -a}
