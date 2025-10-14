method CubeSurfaceArea(size: int) returns (area: int)
    requires size > 0
    ensures area == 6 * size * size
{
    // size > 0
    // area will be assigned as per the postcondition
    area := 6 * size * size;
    assert area == 6 * size * size;
}
function abs(a: real) : real {if a>0.0 then a else -a}
