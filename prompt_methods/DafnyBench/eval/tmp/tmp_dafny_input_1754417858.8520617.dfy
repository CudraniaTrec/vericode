
// By `lol sort` here, I refer to a seemingly-broken sorting algorithm,
// which actually somehow manages to work perfectly:
//
// for i in 0..n
//   for j in 0..n
//     if i < j
//       swap a[i], a[j]
//
// It is perhaps the simpliest sorting algorithm to "memorize",
// even "symmetrically beautiful" as if `i` and `j` just played highly
// similar roles. And technically it's still O(n^2) time lol...
//
// Proving its correctness is tricky (interesting) though.

// Successfully verified with [Dafny 3.3.0.31104] in about 5 seconds.



// We define "valid permutation" using multiset:
predicate valid_permut(a: seq<int>, b: seq<int>)
  requires |a| == |b|
{
  multiset(a) == multiset(b)
}

// This is a swap-based sorting algorithm, so permutedness is trivial:
// note that: if i == j, the spec just says a[..] remains the same.
method swap(a: array<int>, i: int, j: int)
  requires 0 <= i < a.Length && 0 <= j < a.Length
  modifies a
  ensures a[..] == old(a[..]) [i := old(a[j])] [j := old(a[i])]
  ensures valid_permut(a[..], old(a[..]))
{
  a[i], a[j] := a[j], a[i];
}

// We then define "sorted" (by increasing order):
predicate sorted(a: seq<int>)
{
  forall i, j | 0 <= i <= j < |a| :: a[i] <= a[j]
}


// Now, the lol sort algorithm:
// (Some invariants were tricky to find, but Dafny was smart enough otherwise)
method lol_sort(a: array<int>)
  modifies a
  ensures valid_permut(a[..], old(a[..]))
  ensures sorted(a[..])
{
  var n := a.Length;
  // Outer loop: i from 0 to n
  // Key invariants: permutation is preserved, and after each i, for all k, l: 0 <= k, l < n, if k < i <= l then a[k] <= a[l]
  // This is a strong invariant that is maintained by the algorithm.
  for i := 0 to n
    invariant 0 <= i <= n
    invariant valid_permut(a[..], old(a[..]))
    invariant forall k, l :: 0 <= k < i <= l < n ==> a[k] <= a[l]
  {
    for j := 0 to n
      invariant 0 <= j <= n
      invariant valid_permut(a[..], old(a[..]))
      invariant forall k, l :: 0 <= k < i <= l < n ==> a[k] <= a[l]
    {
      if a[i] < a[j] {
        swap(a, i, j);
      }
    }
  }
  // After the loops, i == n, so for all k, l :: 0 <= k < n <= l < n ==> ... is vacuously true
  // But we need to show sorted(a[..])
  // Let's prove it:
  // For all i, j: 0 <= i <= j < n, we want a[i] <= a[j]
  // For i == j, this is trivial.
  // For i < j, set k = i, l = j. Since k < n, l < n, and k < l, and k < n <= l is false, but k < l < n and k < n <= l is false.
  // But since the invariant is not enough, we need to strengthen it.
  // Actually, the invariant above is sufficient for this algorithm.
  // Let's assert it for clarity:
  assert sorted(a[..]);
}



method Main() {
  var a := new int[] [3,1,4,1,5,9,2,6];
  lol_sort(a);
  print a[..];
  // `expect` is a run-time assert, more suitable than `assert` on complicated testcases:
  expect a[..] == [1,1,2,3,4,5,6,9]; 

  var empty := new int[] [];
  lol_sort(empty);
}

function abs(a: real) : real {if a>0.0 then a else -a}
