// Helper function to check array equality (assumes order matters)
function method arrayEquals(a: array<int>, b: array<int>): bool
    requires a != null && b != null
    reads a, b
{
    a.Length == b.Length &&
    (forall i :: 0 <= i < a.Length ==> a[i] == b[i])
}

// Main method to remove duplicate numbers (only keep numbers that occur once)
method twoUniqueNums(nums: array<int>) returns (res: array<int>)
    requires nums != null
    ensures res != null
    ensures forall i :: 0 <= i < res.Length ==> 
                (exists k :: 0 <= k < nums.Length && nums[k] == res[i] &&
                   (forall j :: 0 <= j < nums.Length && j != k ==> nums[j] != res[i]))
    ensures res.Length == |set i | 0 <= i < nums.Length && (forall j :: 0 <= j < nums.Length && j != i ==> nums[j] != nums[i])|
    ensures (forall i :: 0 <= i < res.Length ==> (forall j :: 0 <= j < nums.Length ==> (res[i] == nums[j] ==> (forall k :: 0 <= k < nums.Length && k != j ==> nums[k] != res[i]))))
{
    // First pass: Count occurrences using a map from int to int
    var count := map[int]int[];

    var i := 0;
    while i < nums.Length
        invariant 0 <= i <= nums.Length
        invariant count.Keys <= set nums[j] | 0 <= j < i
        decreases nums.Length - i
    {
        var v := nums[i];
        if v in count {
            count[v] := count[v] + 1;
        } else {
            count[v] := 1;
        }
        i := i + 1;
    }

    // Second pass: Collect numbers that occur exactly once, in original order
    var unique := new int[nums.Length];
    var idx := 0;
    i := 0;
    while i < nums.Length
        invariant 0 <= i <= nums.Length
        invariant 0 <= idx <= i
        invariant (forall j :: 0 <= j < idx ==> count[unique[j]] == 1)
        invariant (forall j :: 0 <= j < idx ==> (exists k :: 0 <= k < i && nums[k] == unique[j]))
        invariant (forall m,n :: 0 <= m < n < idx ==> unique[m] != unique[n])
        decreases nums.Length - i
    {
        var v := nums[i];
        if count[v] == 1 {
            // Only add if not already added (avoid duplicates in result, as input may have multiple unique values)
            var already := false;
            var j := 0;
            while j < idx
                invariant 0 <= j <= idx
                invariant !already ==> (forall k :: 0 <= k < j ==> unique[k] != v)
                decreases idx - j
            {
                if unique[j] == v {
                    already := true;
                }
                j := j + 1;
            }
            if !already {
                unique[idx] := v;
                idx := idx + 1;
            }
        }
        i := i + 1;
    }

    // Resize result to correct length
    res := new int[idx];
    i := 0;
    while i < idx
        invariant 0 <= i <= idx
        decreases idx - i
    {
        res[i] := unique[i];
        i := i + 1;
    }
}