method CountUnequalUnorderedPairs(a: seq<int>) returns (count: nat)
    ensures count == |{ (i,j) | 0 <= i < |a|, 0 <= j < i, a[i] != a[j] }|
{
    var n := |a|;
    var res := 0;
    // Iterate over all unordered pairs (i, j) with i > j
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant res == |{ (ii,jj) | 0 <= ii < i, 0 <= jj < ii, a[ii] != a[jj] }|
    {
        var j := 0;
        while j < i
            invariant 0 <= j <= i
            invariant res == |{ (ii,jj) | 0 <= ii < i, 0 <= jj < ii, a[ii] != a[jj] }| + |{ jj | 0 <= jj < j, a[i] != a[jj] }|
        {
            if a[i] != a[j] {
                res := res + 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    count := res;
}