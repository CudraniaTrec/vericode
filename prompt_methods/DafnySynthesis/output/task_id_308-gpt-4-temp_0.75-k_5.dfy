method LargestProducts(arr1: array<int>, arr2: array<int>, count: int) returns (result: seq<int>)
    requires arr1 != null && arr2 != null
    requires arr1.Length > 0 && arr2.Length > 0
    requires 0 < count <= arr1.Length * arr2.Length
    ensures |result| == count
    ensures forall i :: 0 <= i < count ==> exists j, k :: 0 <= j < arr1.Length && 0 <= k < arr2.Length && result[i] == arr1[j] * arr2[k]
    ensures forall i, j :: 0 <= i < j < count ==> result[i] >= result[j]
{
    var products := new int[arr1.Length * arr2.Length];
    var idx := 0;
    // Compute all possible products
    for i := 0 to arr1.Length - 1 {
        for j := 0 to arr2.Length - 1 {
            products[idx] := arr1[i] * arr2[j];
            idx := idx + 1;
        }
    }

    // Sort products in non-increasing order (simple selection sort for clarity)
    // For larger arrays, a priority queue or more efficient sort is preferable.
    for i := 0 to products.Length - 2 {
        var maxIdx := i;
        for j := i + 1 to products.Length - 1 {
            if products[j] > products[maxIdx] {
                maxIdx := j;
            }
        }
        if maxIdx != i {
            var tmp := products[i];
            products[i] := products[maxIdx];
            products[maxIdx] := tmp;
        }
    }

    // Build result sequence of the largest 'count' products
    result := [];
    for i := 0 to count - 1 {
        result := result + [products[i]];
    }
}