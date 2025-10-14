// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file checks that loops between the range and the term of a quantifier
// are properly detected.

predicate P(x: int)

function sumIntsWithP(n: int): int
  ensures sumIntsWithP(n) == (if n <= 0 then 0 else sumIntsWithP(n-1) + (if P(n-1) then n-1 else 0))
{
  if n <= 0 then 0 else sumIntsWithP(n-1) + (if P(n-1) then n-1 else 0)
}

method M(x: int) {
  // This will be flagged as a loop even without looking at the range
  // This requires checking the range for looping terms
  var sum := 0;
  var i := 0;
  while i < x
    invariant 0 <= i <= x
    invariant sum == sumIntsWithP(i)
  {
    if P(i) {
      sum := sum + i;
    }
    i := i + 1;
  }
  assert sum == sumIntsWithP(x);
}

function abs(a: real) : real {if a>0.0 then a else -a}
