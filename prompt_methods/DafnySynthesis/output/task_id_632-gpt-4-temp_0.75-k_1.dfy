// Helper predicate for array equality
function method arrayEquals(a: array<int>, b: array<int>): bool
  requires a != null && b != null
  reads a, b
{
  a.Length == b.Length &&
  (forall i :: 0 <= i < a.Length ==> a[i] == b[i])
}

// Move all zeroes in num_list to the end, preserving order of non-zeros
method moveZero(num_list: array<int>) returns (res: array<int>)
  requires num_list != null
  ensures res != null && res.Length == num_list.Length
  ensures (exists k :: 0 <= k <= res.Length &&
              (forall i :: 0 <= i < k ==> res[i] != 0) &&
              (forall i :: k <= i < res.Length ==> res[i] == 0) &&
              multiset({i: int | 0 <= i < res.Length && res[i] != 0}) ==
              multiset({i: int | 0 <= i < num_list.Length && num_list[i] != 0})
         )
{
  var n := num_list.Length;
  res := new int[n];
  var pos := 0;
  // First copy non-zero elements
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= pos <= i
    invariant (forall j :: 0 <= j < pos ==> res[j] != 0)
    invariant (forall j :: 0 <= j < pos ==> exists k :: 0 <= k < i && num_list[k] != 0 && num_list[k] == res[j])
    invariant multiset({j: int | 0 <= j < pos && res[j] != 0}) <= multiset({k: int | 0 <= k < i && num_list[k] != 0})
    decreases n - i
  {
    if num_list[i] != 0 {
      res[pos] := num_list[i];
      pos := pos + 1;
    }
    i := i + 1;
  }
  // Fill the rest with zeros
  i := pos;
  while i < n
    invariant pos <= i <= n
    invariant (forall j :: 0 <= j < pos ==> res[j] != 0)
    invariant (forall j :: pos <= j < i ==> res[j] == 0)
    decreases n - i
  {
    res[i] := 0;
    i := i + 1;
  }
}