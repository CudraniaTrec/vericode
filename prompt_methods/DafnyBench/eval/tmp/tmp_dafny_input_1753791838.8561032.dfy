method CylinderLateralSurfaceArea(radius: real, height: real) returns (area: real)
    requires radius > 0.0 && height > 0.0
    ensures area == 2.0 * (radius * height) * 3.14
{
    // radius > 0.0 && height > 0.0
    assert radius > 0.0;
    assert height > 0.0;
    area := 2.0 * (radius * height) * 3.14;
    assert area == 2.0 * (radius * height) * 3.14;
}
function abs(a: real) : real {if a>0.0 then a else -a}
