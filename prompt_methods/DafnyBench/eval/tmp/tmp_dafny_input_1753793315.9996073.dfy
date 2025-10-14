method SphereVolume(radius: real) returns (volume: real)
    requires radius > 0.0
    ensures volume == 4.0/3.0 * 3.1415926535 * radius * radius * radius
{
    // radius > 0.0 by precondition
    assert radius > 0.0;
    // Compute the volume using the formula for the volume of a sphere
    volume := 4.0/3.0 * 3.1415926535 * radius * radius * radius;
    // Postcondition holds by direct assignment
    assert volume == 4.0/3.0 * 3.1415926535 * radius * radius * radius;
}
function abs(a: real) : real {if a>0.0 then a else -a}
