
predicate SplitPoint(a: array<int>, n: int)
    reads a
    requires 0 <= n <= a.Length
{
    forall i, j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
}

method SelectionSort(a: array<int>)
    modifies a
    ensures forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures multiset(a[..]) == old(multiset(a[..]))
{
    var n := 0;
    while n != a.Length
        invariant 0 <= n <= a.Length
        invariant forall i, j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
        invariant multiset(a[..]) == old(multiset(a[..]))
    {
        var mindex := n;
        var m := n;
        while m != a.Length
            invariant n <= m <= a.Length
            invariant n <= mindex < a.Length
            invariant forall k :: n <= k < m ==> a[mindex] <= a[k]
        {
            if a[m] < a[mindex] {
                mindex := m;
            }
            m := m + 1;
        }
        a[n], a[mindex] := a[mindex], a[n];
        n := n + 1;
    }
}

method QuickSort(a: array<int>)
    modifies a
    ensures forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures multiset(a[..]) == old(multiset(a[..]))
{
    QuickSortAux(a, 0, a.Length);
}

twostate predicate SwapFrame(a: array<int>, lo: int, hi: int)
    requires 0 <= lo <= hi <= a.Length
    reads a
{
    (forall i :: 0 <= i < lo || hi <= i < a.Length ==> a[i] == old(a[i])) && multiset(a[..]) == old(multiset(a[..]))
}

method QuickSortAux(a: array<int>, lo: int, hi: int)
    requires 0 <= lo <= hi <= a.Length
    requires SplitPoint(a, lo) && SplitPoint(a, hi)
    modifies a
    ensures forall i, j :: lo <= i < j < hi ==> a[i] <= a[j]
    ensures SwapFrame(a, lo, hi)
    ensures SplitPoint(a, lo) && SplitPoint(a, hi)
    decreases hi - lo
{
    if 2 <= hi - lo {
        var p := Partition(a, lo, hi);
        QuickSortAux(a, lo, p);
        QuickSortAux(a, p + 1, hi);
    }
}

method Partition(a: array<int>, lo: int, hi: int) returns (p: int)
    requires 0 <= lo < hi <= a.Length
    requires SplitPoint(a, lo) && SplitPoint(a, hi)
    modifies a
    ensures lo <= p < hi
    ensures forall i :: lo <= i < p ==> a[i] < a[p]
    ensures forall i :: p <= i < hi ==> a[p] <= a[i]
    ensures SplitPoint(a, lo) && SplitPoint(a, hi)
    ensures SwapFrame(a, lo, hi)
{
    var pivot := a[lo];
    var m := lo + 1;
    var n := hi;
    while m < n
        invariant lo + 1 <= m <= n <= hi
        invariant forall i :: lo + 1 <= i < m ==> a[i] < pivot
        invariant forall i :: n <= i < hi ==> a[i] >= pivot
        invariant a[lo] == pivot
        invariant multiset(a[lo..hi]) == old(multiset(a[lo..hi]))
        invariant SplitPoint(a, lo) && SplitPoint(a, hi)
        invariant SwapFrame(a, lo, hi)
        decreases n - m
    {
        if a[m] < pivot {
            m := m + 1;
        } else {
            a[m], a[n-1] := a[n-1], a[m];
            n := n - 1;
        }
    }
    a[lo], a[m - 1] := a[m - 1], a[lo];
    p := m - 1;
    // assert lo <= p < hi;
    // assert forall i :: lo <= i < p ==> a[i] < a[p];
    // assert forall i :: p < i < hi ==> a[p] <= a[i];
    // assert SplitPoint(a, lo) && SplitPoint(a, hi);
    // assert SwapFrame(a, lo, hi);
    return p;
}

function abs(a: real) : real {if a>0.0 then a else -a}
