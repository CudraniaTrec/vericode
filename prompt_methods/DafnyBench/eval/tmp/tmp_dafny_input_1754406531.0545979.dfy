method CylinderLateralSurfaceArea(radius: real, height: real) returns (area: real)
    requires radius > 0.0 && height > 0.0
    ensures area == 2.0 * (radius * height) * 3.14
{
    // radius and height are both strictly positive
    assert radius > 0.0;
    assert height > 0.0;
    // Compute the lateral surface area
    area := 2.0 * (radius * height) * 3.14;
    // area must be strictly positive
    assert area > 0.0;
    // area must equal the specified formula
    assert area == 2.0 * (radius * height) * 3.14;
}
function abs(a: real) : real {if a>0.0 then a else -a}
