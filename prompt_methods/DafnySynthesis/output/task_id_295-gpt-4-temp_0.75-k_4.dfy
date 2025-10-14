method SumOfDivisors(n: nat) returns (sum: nat)
  ensures sum == (if n == 0 then 0 else (sum d: nat {:trigger n % d == 0} :: 1 <= d <= n && n % d == 0))
{
  if n == 0 {
    sum := 0;
    return;
  }
  sum := 0;
  var d := 1;
  while d <= n
    invariant 1 <= d <= n + 1
    invariant sum == (sum i: nat :: 1 <= i < d && n % i == 0)
  {
    if n % d == 0 {
      sum := sum + d;
    }
    d := d + 1;
  }
}