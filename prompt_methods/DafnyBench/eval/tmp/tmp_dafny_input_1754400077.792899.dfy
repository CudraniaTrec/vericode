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
    invariant forall i :: 0 <= i < a ==> X[i] <= p
    invariant multiset(X[..]) == multiset(old(X[..]))
  { 
    a := a+1;
  }
  
  b := a+1;

  // At loop entry, a <= b <= n and a <= n, so a <= b <= n holds.
  // However, we must ensure that forall i :: a <= i < b ==> X[i] > p holds on entry.
  // On entry, b = a+1, so the range a <= i < b is at most one element (i=a).
  // But at this point, X[a] may not be > p, so we need to weaken the invariant for the first iteration.
  // Instead, we can use: forall i :: a < i < b ==> X[i] > p
  // This is vacuously true on entry, since b = a+1, so a < i < b is empty.

  while ( b<n )
    invariant 0 <= a <= b <= n
    invariant forall i :: 0 <= i < a ==> X[i] <= p
    invariant forall i :: a < i < b ==> X[i] > p
    invariant multiset(X[..]) == multiset(old(X[..]))
  { 
    if ( X[b] <= p ) {
      var t := X[b]; 
      X[b] := X[a]; 
      X[a] := t; 
      a := a+1;
      // After swap, X[a-1] == t <= p, and the segment a < i < b still holds X[i] > p except at i=a-1, which is now <= p and included in [0,a).
    }
    b := b+1;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
