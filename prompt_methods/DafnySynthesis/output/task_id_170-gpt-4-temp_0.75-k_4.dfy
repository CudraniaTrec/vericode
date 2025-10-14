// Dafny Code

method SumInRange(arr: array<int>, start: int, end: int) returns (sum: int)
    requires arr != null
    requires 0 <= start <= end < arr.Length
    ensures sum == (if start > end then 0 else (sum i | start <= i <= end :: arr[i]))
{
    sum := 0;
    var i := start;
    while i <= end
        invariant start <= i <= end + 1
        invariant sum == (sum j | start <= j < i :: arr[j])
    {
        sum := sum + arr[i];
        i := i + 1;
    }
}