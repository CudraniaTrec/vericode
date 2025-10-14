
// Sorting: 
//        Pre/Post Condition Issues - An investigation 
//                                      -- Stephanie McIntyre
// Based on examples in class 

// First Attempt at specifying requirements for sorting array A in incrementing order
// We want our Hoare triple of (|Pre-Condition|) Code (|Post-Condition|) to hold iff A is properly sorted.

method sort(A: array<int>, n: int)
modifies A; requires n==A.Length;
/* Pre-Condition */   requires n>=0;            
/* Post-Condition */  ensures forall i,j:: 0<=i<=j<n ==> A[i]<=A[j];  //This states that A is sorted.

//Can we write code that does not sort A that still satisfies the requirements? 
//Consider the following program:
{
  var k := 0;
  // Strongest possible loop invariant:
  //  - 0 <= k <= n
  //  - For all i in 0..k-1, A[i] == i
  //  - For all i,j in 0..k-1, i <= j ==> A[i] <= A[j]
  //  - For all i,j in 0..n-1, if i < k <= j, then A[i] <= A[j] (since A[j] is uninitialized, but A[i] == i and A[j] will be set to j)
  while(k<n)
    invariant 0 <= k <= n;
    invariant forall i :: 0 <= i < k ==> A[i] == i;
    invariant forall i, j :: 0 <= i <= j < k ==> A[i] <= A[j];
    invariant forall i, j :: 0 <= i < k <= j < n ==> A[i] <= k;
  {
    A[k] := k;
    assert 0 <= k < n;
    assert forall i :: 0 <= i < k ==> A[i] == i;
    k := k+1;
  }
  // Post-loop assertion: for all i in 0..n-1, A[i] == i
  assert forall i :: 0 <= i < n ==> A[i] == i;
  // Postcondition: for all 0 <= i <= j < n, A[i] <= A[j]
  assert forall i, j :: 0 <= i <= j < n ==> A[i] <= A[j];
}

function abs(a: real) : real {if a>0.0 then a else -a}
