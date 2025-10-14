method CylinderVolume(radius: real, height: real) returns (volume: real)
    requires radius >= 0.0 && height >= 0.0
    ensures volume == 3.14159265358979323846 * radius * radius * height
{
    var pi := 3.14159265358979323846;
    volume := pi * radius * radius * height;
}