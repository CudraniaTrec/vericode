method CylinderSurfaceArea(radius: real, height: real) returns (area: real)
    requires radius > 0.0 && height > 0.0
    ensures area == 2.0 * 3.14159265358979323846 * radius * (radius + height)
{
    // radius > 0.0 && height > 0.0 by precondition
    assert radius > 0.0;
    assert height > 0.0;
    area := 2.0 * 3.14159265358979323846 * radius * (radius + height);
    assert area == 2.0 * 3.14159265358979323846 * radius * (radius + height);
}
function abs(a: real) : real {if a>0.0 then a else -a}
