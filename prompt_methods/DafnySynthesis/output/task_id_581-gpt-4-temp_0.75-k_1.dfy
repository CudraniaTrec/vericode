//Dafny Code

method SurfaceAreaOfSquarePyramid(baseEdge: real, height: real) returns (surfaceArea: real)
    requires baseEdge >= 0.0
    requires height >= 0.0
    ensures surfaceArea >= 0.0
{
    // The area of the base is baseEdge * baseEdge
    var baseArea := baseEdge * baseEdge;

    // The slant height l = sqrt((baseEdge/2)^2 + height^2)
    var halfBase := baseEdge / 2.0;
    var slantHeight := sqrt(halfBase * halfBase + height * height);

    // The area of one triangular face is (baseEdge * slantHeight)/2
    // There are 4 sides: lateralArea = 4 * (baseEdge * slantHeight)/2 = 2 * baseEdge * slantHeight
    var lateralArea := 2.0 * baseEdge * slantHeight;

    surfaceArea := baseArea + lateralArea;
}