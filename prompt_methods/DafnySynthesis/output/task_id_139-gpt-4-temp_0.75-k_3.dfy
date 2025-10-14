//Dafny Code

method Circumference(radius: real) returns (c: real)
    requires radius >= 0.0
    ensures c == 2.0 * 3.141592653589793 * radius
{
    c := 2.0 * 3.141592653589793 * radius;
}