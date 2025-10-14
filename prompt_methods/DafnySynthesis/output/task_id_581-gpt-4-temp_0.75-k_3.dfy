//Dafny Code

method SurfaceAreaSquarePyramid(baseEdge: real, height: real) returns (surfaceArea: real)
    requires baseEdge > 0.0 && height > 0.0
    ensures surfaceArea == baseEdge * baseEdge + 2.0 * baseEdge * sqrt((baseEdge / 2.0) * (baseEdge / 2.0) + height * height)
{
    var baseArea := baseEdge * baseEdge;
    var slantHeight := sqrt((baseEdge / 2.0) * (baseEdge / 2.0) + height * height);
    var lateralArea := 2.0 * baseEdge * slantHeight;
    surfaceArea := baseArea + lateralArea;
}