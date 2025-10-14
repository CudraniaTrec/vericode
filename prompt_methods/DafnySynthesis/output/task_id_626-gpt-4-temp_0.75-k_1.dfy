method LargestInscribedTriangleArea(r: real) returns (area: real)
    requires r > 0.0
    ensures area == r * r
{
    // The largest inscribed triangle in a semicircle is the right triangle
    // with its base as the diameter and its third vertex on the semicircle arch.
    // The area is (1/2) * base * height
    // base = 2*r (diameter)
    // height = r (since the topmost point is at height r)
    area := 0.5 * (2.0 * r) * r;
}