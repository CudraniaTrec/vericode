method CubeVolume(size: int) returns (volume: int)
    requires size > 0
    ensures volume == size * size * size
{
    // size > 0
    assert size > 0;
    volume := size * size * size;
    assert volume == size * size * size;
}
function abs(a: real) : real {if a>0.0 then a else -a}
