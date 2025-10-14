method DegreesToRadians(degrees: real) returns (radians: real)
    ensures radians == degrees * 3.14159265358979323846 / 180.0
{
    // Strongest postcondition is already specified.
    // Add assertion to check the assignment.
    assert degrees * 3.14159265358979323846 / 180.0 == degrees * 3.14159265358979323846 / 180.0;
    radians := degrees * 3.14159265358979323846 / 180.0;
    assert radians == degrees * 3.14159265358979323846 / 180.0;
}
function abs(a: real) : real {if a>0.0 then a else -a}
