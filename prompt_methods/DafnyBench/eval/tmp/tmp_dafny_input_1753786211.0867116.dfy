function Stairs(n: nat): nat {
  if n <= 1 then 1 else Stairs(n - 2) + Stairs(n - 1)
}

// A simple specification
method ClimbStairs(n: nat) returns (r: nat)
  ensures r == Stairs(n)
{
  var a, b := 1, 1;
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant a == Stairs(i - 1)
    invariant b == Stairs(i)
    decreases n - i
  {
    a, b := b, a + b;
    i := i + 1;
  }
  // At this point, i == n, so b == Stairs(n)
  r := b;
}
function abs(a: real) : real {if a>0.0 then a else -a}
