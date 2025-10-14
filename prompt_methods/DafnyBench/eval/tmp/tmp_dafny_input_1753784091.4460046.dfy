
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
  // Invariant: 0 <= k <= n
  // Invariant: forall i,j :: 0 <= i <= j < k ==> A[i] <= A[j]
  while(k<n)
    invariant 0 <= k <= n
    invariant forall i,j :: 0 <= i <= j < k ==> A[i] <= A[j]
  {
    A[k] := k;
    k := k+1;
    // Assert that after assignment, the invariant holds for k
    assert forall i,j :: 0 <= i <= j < k ==> A[i] <= A[j];
  }
  // Assert that the postcondition holds
  assert forall i,j :: 0 <= i <= j < n ==> A[i] <= A[j];
}

function abs(a: real) : real {if a>0.0 then a else -a}
