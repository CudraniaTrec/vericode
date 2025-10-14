// Quicksort Partition -- Stephanie McIntyre
// Based on examples in class 
// Parts have been modified cause you know, arrays are different...
   
method QuicksortPartition(X: array<int>, n: int, p: int) returns (a: int, b: int)
  modifies X;
/*Pre-Condition*/   requires X.Length>=1 && n == X.Length;
/*Post-Condition*/  ensures b>=n;
                    ensures forall x:: 0<=x<a<n ==> X[x] <= p;
                    ensures forall x:: a==n || (0<=a<=x<n ==> X[x] > p);
                    ensures multiset(X[..])==multiset(old(X[..]))           //This says the new X is a permutation of our old version of X.
{
  a := 0;
  while ( a < n && X[a] <= p ) 
    invariant 0 <= a <= n
    invariant forall x :: 0 <= x < a ==> X[x] <= p
    invariant multiset(X[..]) == multiset(old(X[..]))
  { 
    a := a+1;
  }
  
  b := a+1;

  // At loop entry, a <= b <= n, but we do NOT know forall x :: a <= x < b ==> X[x] > p,
  // because X[a] is not guaranteed to be > p unless a == n.
  // So, we must weaken the invariant to allow a == n (no elements in [a, b)).
  // We also need to ensure that a <= n and b >= a+1 always hold.

  while ( b<n )
    invariant 0 <= a <= b <= n
    invariant forall x :: 0 <= x < a ==> X[x] <= p
    invariant a == n || forall x :: a <= x < b ==> X[x] > p
    invariant multiset(X[..]) == multiset(old(X[..]))
  { 
    if ( X[b] <= p ) {
      var t := X[b]; 
      X[b] := X[a]; 
      X[a] := t; 
      a := a+1;
    }
    b := b+1;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
