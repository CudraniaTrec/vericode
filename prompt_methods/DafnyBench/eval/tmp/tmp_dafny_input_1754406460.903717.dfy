method CircleCircumference(radius: real) returns (circumference: real)
    requires radius > 0.0
    ensures circumference == 2.0 * 3.14159265358979323846 * radius
{
    // radius > 0.0 by precondition
    assert radius > 0.0;
    circumference := 2.0 * 3.14159265358979323846 * radius;
    assert circumference == 2.0 * 3.14159265358979323846 * radius;
}
function abs(a: real) : real {if a>0.0 then a else -a}
