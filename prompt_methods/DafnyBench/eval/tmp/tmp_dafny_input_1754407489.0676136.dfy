method SphereSurfaceArea(radius: real) returns (area: real)
    requires radius > 0.0
    ensures area == 4.0 * 3.14159265358979323846 * radius * radius
{
    // radius > 0.0 by precondition
    assert radius > 0.0;
    // Calculate area
    area := 4.0 * 3.14159265358979323846 * radius * radius;
    // area == 4.0 * pi * r^2
    assert area == 4.0 * 3.14159265358979323846 * radius * radius;
}
function abs(a: real) : real {if a>0.0 then a else -a}
