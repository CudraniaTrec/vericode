//Dafny Code

method CenteredHexagonalNumber(n: nat) returns (res: nat)
    ensures res == 3 * n * (n - 1) + 1
{
    res := 3 * n * (n - 1) + 1;
}