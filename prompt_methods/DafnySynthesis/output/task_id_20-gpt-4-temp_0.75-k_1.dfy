// Dafny Code

method IsWoodball(n: int) returns (isWoodball: bool)
    ensures isWoodball == (n > 0 && n % 11 == 0)
{
    // A "woodball" number is defined as a positive integer divisible by 11
    if n > 0 && n % 11 == 0 {
        isWoodball := true;
    } else {
        isWoodball := false;
    }
}