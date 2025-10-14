method AreaOfLargestTriangleInSemicircle(radius: int) returns (area: int)
    requires radius > 0
    ensures area == radius * radius
{
    // The largest triangle that can be inscribed in a semicircle of radius r has area r^2
    assert radius > 0;
    area := radius * radius;
    assert area == radius * radius;
}
function abs(a: real) : real {if a>0.0 then a else -a}
