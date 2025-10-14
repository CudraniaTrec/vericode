
predicate sorted(a: array?<int>, l: int, u: int)
    reads a
    requires a != null
    {
    forall i, j :: 0 <= l <= i <= j <= u < a.Length ==> a[i] <= a[j]
    }

method BinarySearch(a: array?<int>, key: int)
    returns (index: int)
    requires a != null && sorted(a,0,a.Length-1);
    ensures index >= 0 ==> index < a.Length && a[index] == key;
    ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key;
{
    var low := 0;
    var high := a.Length;
    while (low < high)
        invariant 0 <= low <= high <= a.Length
        invariant forall i :: 0 <= i < low ==> a[i] < key
        invariant forall i :: high <= i < a.Length ==> a[i] > key
        invariant forall i :: low <= i < high ==> true // all possible
        decreases high - low
    {
        var mid := (low + high) / 2;
        assert 0 <= mid < a.Length;
        if (a[mid] < key) {
            assert low <= mid < high;
            low := mid + 1;
        }
        else if (key < a[mid]) {
            assert low <= mid < high;
            high := mid;
        }
        else {
            assert a[mid] == key;
            return mid;
        }
    }
    assert forall k :: 0 <= k < a.Length ==> a[k] != key;
    return -1;
}

function abs(a: real) : real {if a>0.0 then a else -a}
