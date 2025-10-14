//Dafny Code

method OctagonalNumber(n: nat) returns (o: nat)
    ensures o == n * (3 * n - 2)
{
    o := n * (3 * n - 2);
}