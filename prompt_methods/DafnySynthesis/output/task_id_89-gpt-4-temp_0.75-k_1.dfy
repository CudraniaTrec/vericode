method ClosestSmaller(n: int) returns (result: int)
    ensures result < n
    ensures result == n - 1
{
    result := n - 1;
}