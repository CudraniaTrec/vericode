
// RUN: %testDafnyForEachResolver "%s" -- --warn-deprecation:false


// A version of Turing's additive factorial program [Dr. A. Turing, "Checking a large routine",
// In "Report of a Conference of High Speed Automatic Calculating Machines", pp. 67-69, 1949].

ghost function Factorial(n: nat): nat
{
  if n == 0 then 1 else n * Factorial(n-1)
}

method AdditiveFactorial(n: nat) returns (u: nat)
  ensures u == Factorial(n);
{
  u := 1;
  var r := 0;
  while (r < n)
    invariant 0 <= r <= n
    invariant u == Factorial(r)
  {
    var v := u;
    var s := 1;
    while (s <= r)
      invariant 1 <= s <= r+1
      invariant u == v * s
      invariant v == Factorial(r)
    {
      u := u + v;
      s := s + 1;
    }
    assert u == Factorial(r+1);
    r := r + 1;
  }
  assert u == Factorial(n);
}

// Hoare's FIND program [C.A.R. Hoare, "Proof of a program: FIND", CACM 14(1): 39-45, 1971].
// The proof annotations here are not the same as in Hoare's article.

// In Hoare's words:
//   This program operates on an array A[1:N], and a value of f (1 <= f <= N).
//   Its effect is to rearrange the elements of A in such a way that:
//     forall p,q (1 <= p <= f <= q <= N ==> A[p] <= A[f] <= A[q]).
//
// Here, we use 0-based indices, so we would say:
//   This method operates on an array A[0..N], and a value of f (0 <= f < N).
//   Its effect is to rearrange the elements of A in such a way that:
//     forall p,q :: 0 <= p <= f <= q < N ==> A[p] <= A[f] <= A[q]).

method FIND(A: array<int>, N: int, f: int)
  requires A.Length == N;
  requires 0 <= f < N;
  modifies A;
  ensures forall p,q :: 0 <= p <= f <= q < N ==> A[p] <= A[q];
{
  var m, n := 0, N-1;
  while (m < n)
    invariant 0 <= m <= f+1
    invariant f-1 <= n < N
    invariant 0 <= m && n < N
    invariant forall p,q :: 0 <= p < m && n < q < N ==> A[p] <= A[q]
    invariant forall p :: 0 <= p < m ==> A[p] <= A[f]
    invariant forall q :: n < q < N ==> A[f] <= A[q]
  {
    var r, i, j := A[f], m, n;
    while (i <= j)
      invariant m <= i <= j+1 <= n+1
      invariant m <= m && n <= n
      invariant forall k :: m <= k < i ==> A[k] <= r
      invariant forall k :: j < k <= n ==> r <= A[k]
      invariant forall p,q :: 0 <= p < m && n < q < N ==> A[p] <= A[q]
      invariant forall p :: 0 <= p < m ==> A[p] <= r
      invariant forall q :: n < q < N ==> r <= A[q]
      // the following two invariants capture (and follow from) the fact that the array is not modified outside the [m:n] range
      // the following invariant is used to prove progress of the outer loop
    {
      ghost var firstIteration := i==m && j==n;
      while (A[i] < r)
        invariant m <= i <= n+1
        invariant forall k :: m <= k < i ==> A[k] < r
        invariant forall k :: j < k <= n ==> r <= A[k]
      { i := i + 1; }

      while (r < A[j])
        invariant m-1 <= j <= n
        invariant forall k :: m <= k <= j ==> A[k] < r ==> k < i
        invariant forall k :: j < k <= n ==> r < A[k]
      { j := j - 1; }

      if (i <= j) {
        var w := A[i]; A[i] := A[j]; A[j] := w;  // swap A[i] and A[j] (which may be referring to the same location)
        i, j := i + 1, j - 1;
      }
    }

    if (f <= j) {
      n := j;
    } else if (i <= f) {
      m := i;
    } else {
      break;  // Hoare used a goto
    }
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
