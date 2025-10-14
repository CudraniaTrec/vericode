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
      invariant u == v * s
      invariant v == Factorial(r)
      decreases r - s + 1
    {
      u := u + v;
      s := s + 1;
    }
    r := r + 1;
  }
}

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
    var r := A[f];
    var i := m;
    var j := n;
    while (i <= j)
      invariant m <= i <= j+1 <= n+1
      invariant forall k :: m <= k < i ==> A[k] <= r
      invariant forall k :: j < k <= n ==> r <= A[k]
      invariant forall p,q :: 0 <= p < m && n < q < N ==> A[p] <= A[q]
      decreases j - i + 1
    {
      while (i <= j && A[i] < r)
        invariant m <= i <= j+1 <= n+1
        invariant forall k :: m <= k < i ==> A[k] < r
        invariant forall k :: j < k <= n ==> r <= A[k]
        decreases j - i + 1
      {
        i := i + 1;
      }

      while (i <= j && r < A[j])
        invariant m-1 <= j <= n
        invariant forall k :: m <= k < i ==> A[k] < r
        invariant forall k :: j < k <= n ==> r < A[k]
        decreases j - i + 1
      {
        j := j - 1;
      }

      if (i <= j) {
        var w := A[i]; A[i] := A[j]; A[j] := w;
        i, j := i + 1, j - 1;
      }
    }

    if (f <= j) {
      n := j;
    } else if (i <= f) {
      m := i;
    } else {
      break;
    }
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
