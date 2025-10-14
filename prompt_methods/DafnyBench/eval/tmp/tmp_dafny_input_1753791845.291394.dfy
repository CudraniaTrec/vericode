method CubeVolume(size: int) returns (volume: int)
    requires size > 0
    ensures volume == size * size * size
{
    // size > 0 by precondition
    // size * size > 0 because size > 0
    // size * size * size > 0 because size > 0
    assert size * size > 0;
    assert size * size * size > 0;
    volume := size * size * size;
    assert volume == size * size * size;
}
function abs(a: real) : real {if a>0.0 then a else -a}
