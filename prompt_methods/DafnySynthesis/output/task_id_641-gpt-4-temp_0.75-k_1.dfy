//Dafny Code

method NonagonalNumber(n: nat) returns (num: nat)
    ensures num == n * (7 * n - 5) / 2
{
    num := n * (7 * n - 5) / 2;
}