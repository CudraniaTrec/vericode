
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
{
  var i := 0;
  var j := 0;

  // Outer loop: i goes from 0 to n-2
  while(i < n-1)
    invariant 0 <= i <= n-1
    invariant n == A.Length
    invariant forall k :: 0 <= k < i ==> (forall l :: k < l < n ==> A[k] <= A[l])
    invariant 0 <= j <= n-i-1
  {
    j := 0;
    // Inner loop: j goes from 0 to n-i-2
    while(j < n-i-1)
      invariant 0 <= j <= n-i-1
      invariant 0 <= i < n
      invariant n == A.Length
      invariant forall k :: 0 <= k < i ==> (forall l :: k < l < n ==> A[k] <= A[l])
      invariant forall k :: 0 <= k < j ==> A[k] <= A[j]
    {
      if(A[j]<A[i]){
        var t := A[j];
        A[j] := A[i];
        A[i] := t;
        assert A[j] >= A[i]; // After swap, A[j] >= A[i]
      } 
      j := j+1;
    }
    i := i+1;
  }
}

/*Doesn't my title look all bubbly and cute? I'm trying... */

function abs(a: real) : real {if a>0.0 then a else -a}
