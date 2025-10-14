// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// VSComp 2010, problem 1, compute the sum and max of the elements of an array and prove
// that 'sum <= N * max'.
// Rustan Leino, 18 August 2010.
//
// The problem statement gave the pseudo-code for the method, but did not ask to prove
// that 'sum' or 'max' return as the sum and max, respectively, of the array.  The
// given assumption that the array's elements are non-negative is not needed to establish
// the requested postcondition.

function sumArray(a: array<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= a.Length
  decreases hi - lo
{
  if lo == hi then 0 else a[lo] + sumArray(a, lo + 1, hi)
}

method M(N: int, a: array<int>) returns (sum: int, max: int)
  requires 0 <= N && a.Length == N && (forall k :: 0 <= k && k < N ==> 0 <= a[k]);
  ensures sum <= N * max;
{
  sum := 0;
  max := 0;
  var i := 0;
  while (i < N)
    invariant 0 <= i <= N
    invariant sum == sumArray(a, 0, i)
    invariant (i == 0 ==> max == 0)
    invariant (i > 0 ==> max == MaxSeq(a, i))
    invariant forall j :: 0 <= j < i ==> max >= a[j]
    invariant forall j :: 0 <= j < i ==> 0 <= a[j]
    invariant max >= 0
    invariant sum <= i * max
    decreases N - i
  {
    if (max < a[i]) {
      max := a[i];
    }
    sum := sum + a[i];
    i := i + 1;
  }
}

// Returns the maximum of a[0..i-1], or 0 if i == 0
function MaxSeq(a: array<int>, i: int): int
  requires 0 <= i <= a.Length
  decreases i
{
  if i == 0 then 0 else if i == 1 then a[0] else if MaxSeq(a, i - 1) < a[i - 1] then a[i - 1] else MaxSeq(a, i - 1)
}

method Main()
{
  var a := new int[10];
  a[0] := 9;
  a[1] := 5;
  a[2] := 0;
  a[3] := 2;
  a[4] := 7;
  a[5] := 3;
  a[6] := 2;
  a[7] := 1;
  a[8] := 10;
  a[9] := 6;
  var s, m := M(10, a);
  print "N = ", a.Length, "  sum = ", s, "  max = ", m, "\n";
}
function abs(a: real) : real {if a>0.0 then a else -a}
