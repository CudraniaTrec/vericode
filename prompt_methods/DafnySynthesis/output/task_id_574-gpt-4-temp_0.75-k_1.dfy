//Dafny Code

method SurfaceAreaCylinder(radius: real, height: real) returns (surfaceArea: real)
    requires radius >= 0.0 && height >= 0.0
    ensures surfaceArea == 2.0 * 3.141592653589793 * radius * (radius + height)
{
    // Surface area formula: 2 * pi * r * (r + h)
    var pi := 3.141592653589793;
    surfaceArea := 2.0 * pi * radius * (radius + height);
}