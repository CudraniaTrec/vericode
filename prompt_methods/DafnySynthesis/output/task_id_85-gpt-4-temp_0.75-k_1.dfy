//Dafny Code

method SurfaceAreaOfSphere(radius: real) returns (area: real)
    requires radius >= 0.0
    ensures area == 4.0 * 3.141592653589793 * radius * radius
{
    var pi := 3.141592653589793;
    area := 4.0 * pi * radius * radius;
}