// Sorting: 
//        Pre/Post Condition Issues - An investigation 
//                                      -- Stephanie McIntyre
// Based on examples in class 
// The following is just plain old bubble sort.
//
// Can you find the invariants for the while loops?
// Can you annotate this?
// What about the pre/post-conditions?

method BubbleSort(A: array<int>, n: int)
modifies A;
requires A.Length>=0 && n==A.Length;
ensures multiset(A[..]) == multiset(old(A[..]))
ensures forall k: int, l: int :: 0 <= k < l < n ==> A[k] <= A[l]
{
  var i := 0;

  while(i < n-1)
    invariant 0 <= i <= n-1
    invariant multiset(A[..]) == multiset(old(A[..]))
    invariant forall k: int, l: int :: n-i <= k < l < n ==> A[k] <= A[l]
  {
    var j := 0;
    while(j < n-i-1)
      invariant 0 <= j <= n-i-1
      invariant n == A.Length
      invariant multiset(A[..]) == multiset(old(A[..]))
      invariant forall k: int, l: int :: n-i <= k < l < n ==> A[k] <= A[l]
    {
      if(A[j] > A[j+1]){
        var t := A[j];
        A[j] := A[j+1];
        A[j+1] := t;
      } 
      j := j+1;
    }
    i := i+1;
  }
}

/*Doesn't my title look all bubbly and cute? I'm trying... */

function abs(a: real) : real {if a>0.0 then a else -a}
