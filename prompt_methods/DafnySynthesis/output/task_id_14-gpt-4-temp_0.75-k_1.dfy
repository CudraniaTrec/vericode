method PrismVolume(base: real, height: real, length: real) returns (volume: real)
    requires base >= 0.0 && height >= 0.0 && length >= 0.0
    ensures volume == 0.5 * base * height * length
{
    volume := 0.5 * base * height * length;
}