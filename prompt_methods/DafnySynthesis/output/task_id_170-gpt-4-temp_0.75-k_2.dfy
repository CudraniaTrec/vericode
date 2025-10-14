// Dafny Code

method SumInRange(arr: array<int>, start: int, end: int) returns (sum: int)
    requires arr != null
    requires 0 <= start <= end <= arr.Length
    ensures sum == (if start == end then 0 else sum arr[i | start <= i < end])
{
    sum := 0;
    var i := start;
    while i < end
        invariant start <= i <= end
        invariant sum == sum arr[j | start <= j < i]
    {
        sum := sum + arr[i];
        i := i + 1;
    }
}