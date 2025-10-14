method SquarePyramidSurfaceArea(baseEdge: int, height: int) returns (area: int)
    requires baseEdge > 0
    requires height > 0
    ensures area == baseEdge * baseEdge + 2 * baseEdge * height
{
    // base area = baseEdge * baseEdge
    // lateral area = 2 * baseEdge * height
    assert baseEdge > 0;
    assert height > 0;
    var baseArea := baseEdge * baseEdge;
    var lateralArea := 2 * baseEdge * height;
    assert baseArea == baseEdge * baseEdge;
    assert lateralArea == 2 * baseEdge * height;
    area := baseArea + lateralArea;
    assert area == baseEdge * baseEdge + 2 * baseEdge * height;
}
function abs(a: real) : real {if a>0.0 then a else -a}
