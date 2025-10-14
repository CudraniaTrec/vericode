//Dafny Code

method AreaOfRectangle(length: int, width: int) returns (area: int)
    requires length >= 0 && width >= 0
    ensures area == length * width
{
    area := length * width;
}