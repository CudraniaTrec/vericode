method CylinderVolume(radius: real, height: real) returns (volume: real)
    requires radius > 0.0
    requires height > 0.0
    ensures volume == 3.14159265359 * radius * radius * height
{
    // radius and height are both positive by precondition
    assert radius > 0.0;
    assert height > 0.0;
    // Compute the volume
    volume := 3.14159265359 * radius * radius * height;
    // Assert postcondition
    assert volume == 3.14159265359 * radius * radius * height;
}
function abs(a: real) : real {if a>0.0 then a else -a}
