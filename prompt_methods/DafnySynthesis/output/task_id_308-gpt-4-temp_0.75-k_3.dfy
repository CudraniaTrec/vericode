method LargestProducts(a: array<int>, b: array<int>, count: int) returns (res: seq<int>)
    requires a != null && b != null
    requires |a| > 0 && |b| > 0
    requires 0 <= count <= |a| * |b|
    ensures |res| == count
    ensures forall x :: x in res ==> exists i, j :: 0 <= i < |a| && 0 <= j < |b| && a[i] * b[j] == x
    ensures forall x :: !(x in res) ==> (forall y :: y in res ==> x <= y)
{
    var products := new seq<int>[];
    // Collect all possible products
    for i := 0 to |a| - 1 {
        for j := 0 to |b| - 1 {
            products := products + [a[i] * b[j]];
        }
    }
    // Sort descending
    var sorted := products[..];
    sorted := sorted[..];
    // Bubble sort (Dafny does not support standard library sort)
    var n := |sorted|;
    var arr := new int[n];
    for i := 0 to n-1 {
        arr[i] := sorted[i];
    }
    // Simple selection sort for descending order
    for i := 0 to n-2 {
        var maxIdx := i;
        for j := i+1 to n-1 {
            if arr[j] > arr[maxIdx] {
                maxIdx := j;
            }
        }
        if maxIdx != i {
            var tmp := arr[i];
            arr[i] := arr[maxIdx];
            arr[maxIdx] := tmp;
        }
    }
    res := [];
    for i := 0 to count-1 {
        res := res + [arr[i]];
    }
}