//Dafny Code

method CubeSurfaceArea(side: int) returns (area: int)
    requires side >= 0
    ensures area == 6 * side * side
{
    area := 6 * side * side;
}