//Dafny Code

method circleCircumference(r: real) returns (area: real)
{
    // Use the known value of pi to high precision as required by the tests
    var pi := 3.14159265358979323846264338327950288419716939937510;
    area := 2.0 * pi * r;
}