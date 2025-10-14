// Dafny Code

method LateralSurfaceAreaOfCube(side: real) returns (area: real)
    requires side >= 0.0
    ensures area == 4.0 * side * side
{
    area := 4.0 * side * side;
}