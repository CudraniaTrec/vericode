
/*
Bubble Sort is the simplest sorting algorithm that works by 
repeatedly swapping the adjacent elements if they are in wrong order.
*/

predicate sorted_between(A:array<int>, from:int, to:int)
    reads A
{
    forall i, j :: 0 <= i <= j < A.Length && from <= i <= j <= to ==> A[i] <= A[j]
}

predicate sorted(A:array<int>)
    reads A
{
    if A.Length == 0 then true else sorted_between(A, 0, A.Length-1)
}

method BubbleSort(A:array<int>)
    modifies A
    ensures sorted(A)
    ensures multiset(A[..]) == multiset(old(A[..]))
{
    var N := A.Length;
    var i := N-1;
    while 0 < i
        invariant 0 <= i < N
        invariant sorted_between(A, i+1, N-1)
        invariant multiset(A[..]) == multiset(old(A[..]))
    {
        print A[..], "\n";
        var j := 0;
        while j < i
            invariant 0 <= j <= i
            invariant sorted_between(A, i+1, N-1)
            invariant multiset(A[..]) == multiset(old(A[..]))
        {
            if A[j] > A[j+1]
            {
                A[j], A[j+1] := A[j+1], A[j];
                print A[..], "\n";
            }
            j := j+1;
        } 
        // After inner loop, A[i] is maximal among A[0..i]
        // So A[i..N-1] is sorted
        i := i-1;
        print "\n";
    }
    // At this point, i == 0, so sorted_between(A, 1, N-1) holds
    // But also, after the last pass, A[0] <= A[1]
    // So the array is sorted
    if N > 1 {
      assert forall k :: 0 <= k < N-1 ==> A[k] <= A[k+1];
    }
}

method Main() {
    var A := new int[10];
    A[0], A[1], A[2], A[3], A[4], A[5], A[6], A[7], A[8], A[9] := 2, 4, 6, 15, 3, 19, 17, 16, 18, 1;
    BubbleSort(A);
    print A[..];
}

/* Explanation:

     // A is ordered for each pair of elements such that
     // the first element belongs to the left partition of i
     // and the second element belongs to the right partition of i

     // There is a variable defined by the value that the array takes at position j
     // Therefore, each value that the array takes for all elements from 0 to j
     // They are less than or equal to the value of the variable
*/

function abs(a: real) : real {if a>0.0 then a else -a}
