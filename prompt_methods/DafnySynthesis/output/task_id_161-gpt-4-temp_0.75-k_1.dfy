// Dafny Code

method RemoveElements(a: array<int>, remove: array<int>) returns (result: array<int>)
    ensures forall i :: 0 <= i < result.Length ==> 
        (forall j :: 0 <= j < remove.Length ==> result[i] != remove[j])
    ensures multiset(result[..]) == multiset(a[..]) - multiset(remove[..]) * (multiset(a[..]) * multiset(remove[..]))
{
    // First, collect which elements to keep.
    var temp := new seq<int>[];
    var count := 0;
    for i := 0 to a.Length - 1
        invariant 0 <= i <= a.Length
        invariant count == |temp|
        invariant forall k :: 0 <= k < count ==> 
            (forall j :: 0 <= j < remove.Length ==> temp[k] != remove[j])
    {
        var toRemove := false;
        for j := 0 to remove.Length - 1
            invariant 0 <= j <= remove.Length
            decreases remove.Length - j
        {
            if a[i] == remove[j] {
                toRemove := true;
                break;
            }
        }
        if !toRemove {
            temp := temp + [a[i]];
            count := count + 1;
        }
    }
    // Allocate the result array
    result := new int[temp.Length];
    for i := 0 to temp.Length - 1
        invariant 0 <= i <= temp.Length
        decreases temp.Length - i
    {
        result[i] := temp[i];
    }
}