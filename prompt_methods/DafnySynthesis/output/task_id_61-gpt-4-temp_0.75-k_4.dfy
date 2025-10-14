method CountSubstringsSumEqualsLength(s: seq<int>) returns (count: int)
    requires forall d :: d in s ==> 0 <= d <= 9
    ensures 0 <= count <= |s| * (|s| + 1) / 2
{
    count := 0;
    var n := |s|;

    // For each starting index
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant 0 <= count <= i*n - i*(i-1)/2
    {
        var sum := 0;
        var len := 0;
        var j := i;
        while j < n
            invariant i <= j <= n
            invariant len == j - i
            invariant sum == if len == 0 then 0 else sum
        {
            sum := sum + s[j];
            len := len + 1;
            if sum == len {
                count := count + 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}