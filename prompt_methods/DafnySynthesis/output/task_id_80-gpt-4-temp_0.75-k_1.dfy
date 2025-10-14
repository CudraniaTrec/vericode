method TetrahedralNumber(n: nat) returns (t: nat)
    ensures t == n * (n + 1) * (n + 2) / 6
{
    t := n * (n + 1) * (n + 2) / 6;
}