method search(arr:array<int>) returns (res:int)
    requires arr != null && arr.Length > 0
    ensures exists i :: 0 <= i < arr.Length && (forall j :: 0 <= j < arr.Length && j != i ==> arr[i] != arr[j] || j % 2 == 1 && arr[i] == arr[j]) // There's a unique element
    ensures (forall i :: 0 <= i < arr.Length ==> arr[i] == res ==> (forall j :: 0 <= j < arr.Length && j != i ==> arr[j] != res))
{
    var n := arr.Length;
    var lo := 0;
    var hi := n - 1;
    while lo < hi
        invariant 0 <= lo <= hi < n
    {
        var mid := lo + (hi - lo)/2;
        if mid % 2 == 1 {
            mid := mid - 1;
        }
        var v1:int; var v2:int;
        arr[mid].Read(); arr[mid+1].Read();
        v1 := arr[mid]; v2 := arr[mid+1];
        if v1 == v2 {
            lo := mid + 2;
        } else {
            hi := mid;
        }
    }
    arr[lo].Read();
    res := arr[lo];
}