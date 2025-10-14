//https://stackoverflow.com/questions/69364687/how-to-prove-time-complexity-of-bubble-sort-using-dafny
function NChoose2(n: int): int
{
  n * (n - 1) / 2
}

// sum of all integers in the range [lo, hi)
// (inclusive of lo, exclusive of hi)
function SumRange(lo: int, hi: int): int
{
  if lo >= hi then 0
  else SumRange(lo, hi - 1) + hi - 1
}

// dafny proves this automatically by induction
lemma SumRangeNChoose2(n: nat)
  ensures SumRange(0, n) == NChoose2(n)
{}

// dafny proves this automatically by induction
// (given the correct decreases clause)
lemma SumRangeUnrollLeft(lo: int, hi: int)
  ensures SumRange(lo, hi) ==
          if lo >= hi then 0 else lo + SumRange(lo + 1, hi)
  decreases if hi - lo < 0 then 0 else hi - lo
{}

method BubbleSort(a: array<int>) returns (n: nat) 
  modifies a
  ensures n <= NChoose2(a.Length)
{
  // it simplifies the remaining invariants to handle the empty array here
  if a.Length == 0 { return 0; }  

  var i := a.Length - 1;
  n := 0;

  while i > 0
    invariant 0 <= i < a.Length
    invariant n <= SumRange(i, a.Length)
    invariant forall k: int :: i < k < a.Length ==> a[k-1] <= a[k]
    decreases i
  {
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant n <= SumRange(i, a.Length)
      invariant forall k: int :: i < k < a.Length ==> a[k-1] <= a[k]
      decreases i - j
    {
      if a[j] > a[j+1]
      {
        a[j], a[j+1] := a[j+1], a[j];
        n := n + 1;
      }
      j := j + 1;
    }

    i := i - 1;
  }

  // When i == 0, n <= SumRange(0, a.Length) == NChoose2(a.Length)
  calc <= {
    n;
    SumRange(0, a.Length);
    { SumRangeNChoose2(a.Length); }
    NChoose2(a.Length);
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
