
// Sorts array 'a' using the insertion sort algorithm.
method insertionSort(a: array<int>) 
    modifies a
    ensures isSorted(a, 0, a.Length)
    ensures multiset(a[..]) == multiset(old(a[..]))
{
    var i := 0;
    while i < a.Length 
        invariant 0 <= i <= a.Length
        invariant isSorted(a, 0, i)
        invariant multiset(a[..]) == multiset(old(a[..]))
    {
        var j := i;
        while j > 0 && a[j-1] > a[j] 
            invariant 0 <= j <= i
            invariant isSorted(a, 0, j)
            invariant forall k :: j <= k <= i ==> a[k] >= a[j-1] || j == 0
            invariant multiset(a[..]) == multiset(old(a[..]))
        {
            a[j-1], a[j] := a[j], a[j-1];
            j := j - 1;
        }
        i := i + 1;
    }
}

// Checks if array 'a' is sorted.
predicate isSorted(a: array<int>, from: nat, to: nat)
  reads a
  requires 0 <= from <= to <= a.Length
{
    forall i, j :: from <= i < j < to ==> a[i] <= a[j]
}

// Simple test case to check the postcondition
method testInsertionSort() {
  var a := new int[] [ 9, 4, 3, 6, 8];
  insertionSort(a);
}

function abs(a: real) : real {if a>0.0 then a else -a}
