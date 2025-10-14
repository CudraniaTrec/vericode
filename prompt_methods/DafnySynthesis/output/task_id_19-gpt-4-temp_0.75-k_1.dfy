//Dafny Code

method ContainsDuplicate(arr: array<int>) returns (hasDuplicate: bool)
    ensures hasDuplicate <==> exists i, j :: 0 <= i < j < arr.Length && arr[i] == arr[j]
{
    hasDuplicate := false;
    var n := arr.Length;
    // Brute force nested loop to check for duplicates
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant hasDuplicate <==> exists x, y :: 0 <= x < y < i && arr[x] == arr[y]
    {
        var j := i + 1;
        while j < n
            invariant i+1 <= j <= n
            invariant hasDuplicate <==> exists x, y :: 0 <= x < i && 0 <= y < j && x < y && arr[x] == arr[y]
        {
            if arr[i] == arr[j] {
                hasDuplicate := true;
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}