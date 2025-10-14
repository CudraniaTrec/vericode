// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file checks that loops between the range and the term of a quantifier
// are properly detected.

predicate P(x: int)

method M(x: int) {
  var sum := 0;
  var i := 0;
  while i < 10
    invariant 0 <= i <= 10
    invariant sum == (if i == 0 then 0 else sum)
  {
    if P(i) {
      sum := sum + i;
    }
    i := i + 1;
  }
  assert i == 10;
  // sum == sum of all i in 0..9 such that P(i)
  assert sum == (sum j | 0 <= j < 10 && P(j) :: j);
}
function abs(a: real) : real {if a>0.0 then a else -a}
