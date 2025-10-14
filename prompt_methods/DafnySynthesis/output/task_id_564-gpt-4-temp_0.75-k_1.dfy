method countPairs(arr: array<int>, n: int) returns (res: int)
    requires arr != null && arr.Length == n
    ensures res >= 0
{
    // Count total unordered pairs
    var total := n * (n - 1) / 2;

    // Map from int to occurrence count
    var m := map k: int {:trigger true} | false :: 0;
    var distinct := set i | 0 <= i < n :: arr[i];
    // Build counts
    var counts := new int[n];
    // Use a dictionary-like approach with lists, for Dafny
    var uniq := new int[n];
    var uniqCount := 0;
    for i := 0 to n-1 {
        var found := false;
        var idx := 0;
        while idx < uniqCount {
            if uniq[idx] == arr[i] {
                found := true;
                break;
            }
            idx := idx + 1;
        }
        if found {
            counts[idx] := counts[idx] + 1;
        } else {
            uniq[uniqCount] := arr[i];
            counts[uniqCount] := 1;
            uniqCount := uniqCount + 1;
        }
    }
    // Subtract number of pairs with same elements
    var same := 0;
    for i := 0 to uniqCount-1 {
        var c := counts[i];
        same := same + c * (c - 1) / 2;
    }
    res := total - same;
}