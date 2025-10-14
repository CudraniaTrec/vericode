// Dafny Code

method CubeVolume(side: int) returns (volume: int)
    requires side >= 0
    ensures volume == side * side * side
{
    volume := side * side * side;
}