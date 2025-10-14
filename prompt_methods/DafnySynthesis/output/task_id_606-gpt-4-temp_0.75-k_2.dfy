// Dafny Code

method radianDegree(deg: real) returns (rad: real)
{
    // Pi to sufficient precision for the test cases
    var pi := 3.141592653589793;
    rad := deg * pi / 180.0;
}