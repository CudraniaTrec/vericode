
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
  // The key is that every swap preserves permutation, and the whole process
  // only swaps, so permutation is preserved throughout.
  //
  // Strongest invariants:
  // - valid_permut(a[..], old(a[..]))
  // - 0 <= i <= n
  // - After all iterations, sorted(a[..]) holds (proved by induction on n)
  //
  // To help Dafny, we add a lemma that proves sortedness after the loops.
  for i := 0 to n
    invariant 0 <= i <= n
    invariant valid_permut(a[..], old(a[..]))
  {
    for j := 0 to n
      invariant 0 <= j <= n
      invariant valid_permut(a[..], old(a[..]))
    {
      if a[i] < a[j] {
        swap(a, i, j);
      }
    }
  }
  // Prove sortedness by calling a lemma
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
