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
    decreases n - r
  {
    var v := u;
    var s := 1;
    while (s <= r)
      invariant 1 <= s <= r+1
      invariant u == v + (s-1)*v
      decreases r - s + 1
    {
      u := u + v;
      s := s + 1;
    }
    // After inner loop: u == v + r*v == v*(r+1) == Factorial(r)*(r+1) == Factorial(r+1)
    assert u == Factorial(r+1);
    r := r + 1;
  }
  // At loop exit: r == n && u == Factorial(r) ==> u == Factorial(n)
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
    decreases n - m + 1
  {
    var r, i, j := A[f], m, n;
    while (i <= j)
      invariant m <= i <= j+1 <= n+1
      invariant forall p :: m <= p < i ==> A[p] <= r
      invariant forall q :: j < q <= n ==> A[q] >= r
      invariant m == m && n == n // to help Dafny track m,n are unchanged
      decreases j - i + 1
    {
      ghost var firstIteration := i==m && j==n;
      while (i <= j && A[i] < r)
        invariant m <= i <= j+1 <= n+1
        invariant forall p :: m <= p < i ==> A[p] < r
        invariant forall q :: j < q <= n ==> A[q] >= r
        decreases j - i + 1
      { i := i + 1; }

      while (i <= j && r < A[j])
        invariant m <= i <= j+1 <= n+1
        invariant forall p :: m <= p < i ==> A[p] < r
        invariant forall q :: j < q <= n ==> A[q] > r
        decreases j - i + 1
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
