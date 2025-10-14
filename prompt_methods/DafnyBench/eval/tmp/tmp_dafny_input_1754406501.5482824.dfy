method PentagonPerimeter(side: int) returns (perimeter: int)
    requires side > 0
    ensures perimeter == 5 * side
{
    // side > 0 by precondition
    assert side > 0;
    perimeter := 5 * side;
    assert perimeter == 5 * side;
}
function abs(a: real) : real {if a>0.0 then a else -a}
