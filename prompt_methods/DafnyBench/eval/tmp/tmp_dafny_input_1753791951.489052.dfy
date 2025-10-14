method CylinderVolume(radius: real, height: real) returns (volume: real)
    requires radius > 0.0
    requires height > 0.0
    ensures volume == 3.14159265359 * radius * radius * height
{
    assert radius > 0.0;
    assert height > 0.0;
    volume := 3.14159265359 * radius * radius * height;
    assert volume == 3.14159265359 * radius * radius * height;
}
function abs(a: real) : real {if a>0.0 then a else -a}
