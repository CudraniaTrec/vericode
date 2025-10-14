
function sorted(a: array<int>) : bool
    reads a
{
   forall i,j : int :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

method BinarySearch(a: array<int>, x: int) returns (index: int)
    requires sorted(a)
    ensures 0 <= index < a.Length ==> a[index] == x
    ensures index == -1 ==> forall i : int :: 0 <= i < a.Length ==> a[i] != x
{
    var low := 0;
    var high := a.Length - 1;
    var mid := 0;
    
    while (low <= high) 
        invariant 0 <= low <= a.Length
        invariant -1 <= high < a.Length
        invariant high < low || (forall i:int :: 0 <= i < low ==> a[i] < x)
        invariant high < low || (forall i:int :: high < i < a.Length ==> a[i] > x)
        invariant high < low || (forall i:int :: low <= i <= high ==> true)
    {
        mid := (high + low) / 2;
        assert 0 <= mid < a.Length ==> low <= mid <= high;
        if a[mid] < x {
            low := mid + 1;
        }
        else if a[mid] > x {
            high := mid - 1;
        }
        else {
            assert a[mid] == x;
            return mid;
        }
    }
    assert forall i:int :: 0 <= i < a.Length ==> a[i] != x;
    return -1;
}

function abs(a: real) : real {if a>0.0 then a else -a}
