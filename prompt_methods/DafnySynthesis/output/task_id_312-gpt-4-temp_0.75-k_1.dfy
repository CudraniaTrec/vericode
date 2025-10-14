method ConeVolume(radius: real, height: real) returns (volume: real)
    requires radius >= 0.0
    requires height >= 0.0
    ensures volume == (1.0/3.0) * 3.141592653589793 * radius * radius * height
{
    volume := (1.0/3.0) * 3.141592653589793 * radius * radius * height;
}