
method IsSorted(a: array<int>) returns (sorted: bool)
    requires a.Length > 0
    ensures sorted <== forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures !sorted ==> exists i, j :: 0 <= i < j < a.Length && a[i] > a[j]
{
    sorted := true;
    var i: int;
    i := 0;
    // Loop to check for any adjacent pair out of order
    while i < a.Length - 1
        invariant 0 <= i <= a.Length - 1
        invariant sorted ==> forall k, l :: 0 <= k < l <= i ==> a[k] <= a[l]
        invariant !sorted ==> exists k, l :: 0 <= k < l <= i && a[k] > a[l]
    {
        if a[i] > a[i + 1]
        {
            sorted := false;
            break;
        }
        i := i + 1;
    }
    // After the loop, if sorted is still true, then all adjacent pairs are sorted
    // So all pairs are sorted
    // If sorted is false, then we found a counterexample
    sorted := sorted;
}

function abs(a: real) : real {if a>0.0 then a else -a}
