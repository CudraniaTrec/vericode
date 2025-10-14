method DegreesToRadians(degrees: real) returns (radians: real)
    ensures radians == degrees * 3.14159265358979323846 / 180.0
{
    // degrees can be any real number
    // Strongest annotation: assert the postcondition after assignment
    radians := degrees * 3.14159265358979323846 / 180.0;
    assert radians == degrees * 3.14159265358979323846 / 180.0;
}
function abs(a: real) : real {if a>0.0 then a else -a}
