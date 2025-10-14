method SquarePyramidSurfaceArea(baseEdge: int, height: int) returns (area: int)
    requires baseEdge > 0
    requires height > 0
    ensures area == baseEdge * baseEdge + 2 * baseEdge * height
{
    // baseEdge > 0 && height > 0
    assert baseEdge > 0;
    assert height > 0;
    // Compute base area
    var baseArea := baseEdge * baseEdge;
    assert baseArea == baseEdge * baseEdge;
    // Compute lateral area
    var lateralArea := 2 * baseEdge * height;
    assert lateralArea == 2 * baseEdge * height;
    // Total area
    area := baseArea + lateralArea;
    assert area == baseEdge * baseEdge + 2 * baseEdge * height;
}
function abs(a: real) : real {if a>0.0 then a else -a}
