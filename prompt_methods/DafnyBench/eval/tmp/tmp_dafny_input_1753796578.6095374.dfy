method Forbid42(x:int, y:int) returns (z:int)
requires y != 42;
ensures z == x/(42-y);
{
    // 42-y != 0 by precondition
    z := x/(42-y);
    // Postcondition holds by assignment
    return z;
} 

method Allow42(x:int, y:int) returns (z: int, err:bool) 
ensures y != 42 ==> z == x/(42-y) && err == false;
ensures y == 42 ==> z == 0 && err == true;
{
    if (y != 42){
        // 42-y != 0
        z := x/(42-y);
        err := false;
    } else {
        z := 0;
        err := true;
    }
    return z, err;
}

method TEST1()
{
    var c:int := Forbid42(0, 1);

    c := Forbid42(10, 32);

    c := Forbid42(-100, 38);

    var d:int, z:bool := Allow42(0,42);

    d, z := Allow42(-10,42);

    d, z := Allow42(0,1);

    d, z := Allow42(10,32);

    d, z := Allow42(-100,38);
}
function abs(a: real) : real {if a>0.0 then a else -a}
