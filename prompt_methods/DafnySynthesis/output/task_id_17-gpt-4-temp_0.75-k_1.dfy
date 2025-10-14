//Dafny Code

method PerimeterOfSquare(side: int) returns (perimeter: int)
    requires side >= 0
    ensures perimeter == 4 * side
{
    perimeter := 4 * side;
}