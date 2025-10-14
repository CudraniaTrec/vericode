// Dafny Code

method SphereVolume(r: real) returns (volume: real)
    requires r >= 0.0
    ensures volume == (4.0/3.0) * 3.14159265358979323846 * r * r * r
{
    var pi := 3.14159265358979323846;
    volume := (4.0/3.0) * pi * r * r * r;
}