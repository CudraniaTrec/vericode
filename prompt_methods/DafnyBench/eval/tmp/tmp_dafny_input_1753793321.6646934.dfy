method SphereSurfaceArea(radius: real) returns (area: real)
    requires radius > 0.0
    ensures area == 4.0 * 3.14159265358979323846 * radius * radius
{
    // The formula for the surface area of a sphere is 4 * pi * r^2
    assert radius > 0.0;
    area := 4.0 * 3.14159265358979323846 * radius * radius;
    assert area == 4.0 * 3.14159265358979323846 * radius * radius;
}
function abs(a: real) : real {if a>0.0 then a else -a}
