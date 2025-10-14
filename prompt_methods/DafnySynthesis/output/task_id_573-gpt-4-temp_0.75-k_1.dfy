method ProductOfUniqueNumbers(arr: array<int>) returns (prod: int)
    requires arr != null
    ensures 
        // The result is the product of all unique numbers in the array.
        var unique := set i | 0 <= i < arr.Length :: arr[i];
        prod == (if |unique| == 0 then 1 else unique.*)
{
    var seen := set int{};
    prod := 1;
    var foundUnique := false;
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant seen == set j | 0 <= j < i :: arr[j]
        invariant prod == (if |seen| == 0 then 1 else seen.*)
        invariant foundUnique == (|seen| > 0)
    {
        if !(arr[i] in seen) {
            seen := seen + {arr[i]};
            prod := prod * arr[i];
            foundUnique := true;
        }
        i := i + 1;
    }
    if !foundUnique {
        prod := 1;
    }
}

// Helper function to multiply all elements of a set (returns 1 if empty)
function method set.*(s: set<int>): int
    decreases |s|
{
    if |s| == 0 then 1 else var x :| x in s; x * set.*(s - {x})
}