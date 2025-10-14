// Dafny Code

method Directrix(a: real, b: real, c: real) returns (y: real)
    requires a != 0.0
    ensures y == (-1.0 * (b * b - 4.0 * a * c + 1.0)) / (4.0 * a)
{
    // The equation of the directrix of a parabola y = ax^2 + bx + c is:
    // y = (1 - (b^2 - 4ac)) / (4a)
    y := (-1.0 * (b * b - 4.0 * a * c + 1.0)) / (4.0 * a);
}