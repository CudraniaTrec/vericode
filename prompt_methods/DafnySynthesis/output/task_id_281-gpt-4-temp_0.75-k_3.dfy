method AreElementsUnique(arr: array<int>) returns (unique: bool)
    ensures unique <==> (forall i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length && i != j ==> arr[i] != arr[j])
{
    unique := true;
    var n := arr.Length;
    var i := 0;
    while i < n - 1
        invariant 0 <= i <= n - 1
        invariant unique ==> (forall x, y :: 0 <= x < i && 0 <= y < x ==> arr[x] != arr[y])
    {
        var j := i + 1;
        while j < n
            invariant i+1 <= j <= n
            invariant unique ==> (forall y :: 0 <= y < i+1 && 0 <= x < y ==> arr[x] != arr[y])
        {
            if arr[i] == arr[j] {
                unique := false;
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}