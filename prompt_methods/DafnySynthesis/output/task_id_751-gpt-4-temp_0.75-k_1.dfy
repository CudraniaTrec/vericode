// Dafny Code

method IsMinHeap(a: array<int>) returns (isHeap: bool)
    ensures isHeap <==> (forall i :: 0 <= i < a.Length ==>
        ((2*i + 1 < a.Length ==> a[i] <= a[2*i + 1]) &&
         (2*i + 2 < a.Length ==> a[i] <= a[2*i + 2])))
{
    isHeap := true;
    var n := a.Length;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant isHeap ==> (forall j :: 0 <= j < i ==>
            ((2*j + 1 < n ==> a[j] <= a[2*j + 1]) &&
             (2*j + 2 < n ==> a[j] <= a[2*j + 2])))
    {
        if 2*i + 1 < n && a[i] > a[2*i + 1] {
            isHeap := false;
            return;
        }
        if 2*i + 2 < n && a[i] > a[2*i + 2] {
            isHeap := false;
            return;
        }
        i := i + 1;
    }
}