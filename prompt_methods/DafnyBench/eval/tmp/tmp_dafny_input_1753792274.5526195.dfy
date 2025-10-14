method RectangleArea(length: int, width: int) returns (area: int)
    requires length > 0
    requires width > 0
    ensures area == length * width
{
    // length > 0 && width > 0 by precondition
    assert length > 0;
    assert width > 0;
    area := length * width;
    assert area == length * width;
}
function abs(a: real) : real {if a>0.0 then a else -a}
