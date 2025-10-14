
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

method M(N: int, a: array<int>) returns (sum: int, max: int)
  requires 0 <= N && a.Length == N && (forall k :: 0 <= k && k < N ==> 0 <= a[k]);
  ensures sum <= N * max;
{
  sum := 0;
  max := 0;
  var i := 0;
  while (i < N)
    invariant 0 <= i <= N
    invariant sum == (if i == 0 then 0 else (sum := 0; var j := 0; while (j < i) invariant 0 <= j <= i invariant sum == (if j == 0 then 0 else sum + a[j-1]); sum := sum + a[j]; j := j + 1; sum))
    invariant forall k :: 0 <= k < i ==> max >= a[k]
    invariant (i == 0 ==> max == 0)
    invariant (i > 0 ==> max == (function (arr: array<int>, n: int): int { if n == 0 then 0 else (var m := arr[0]; var j := 1; while (j < n) invariant 1 <= j <= n invariant m >= arr[0] && (forall k :: 0 <= k < j ==> m >= arr[k]) invariant (exists k :: 0 <= k < j && m == arr[k]); if m < arr[j] then m := arr[j]; j := j + 1; m) })(a, i))
    invariant sum <= i * max
  {
    if (max < a[i]) {
      max := a[i];
    }
    sum := sum + a[i];
    i := i + 1;
  }
  // At this point: i == N
  // So sum <= N * max by the invariant
  assert sum <= N * max;
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
