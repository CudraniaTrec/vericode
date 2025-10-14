method IsDivisibleBy11(n: int) returns (result: bool)
  ensures result <==> n % 11 == 0
{
  // No preconditions or loops, so no invariants needed.
  assert n % 11 == 0 <==> (n % 11 == 0);
  result := n % 11 == 0;
  assert result <==> n % 11 == 0;
}
function abs(a: real) : real {if a>0.0 then a else -a}
