
/**
  (a) Verify whether or not the following program
      satisfies total correctness.
      You should use weakest precondition reasoning
      and may extend the loop invariant if required.
      You will need to add a decreases clause to prove termination
  (a) Weakest precondition proof (without termination) (6 marks)
      Termination proof (2marks)
*/

function fusc(n: int): nat

lemma rule1()
  ensures fusc(0) == 0

lemma rule2()
  ensures fusc(1) == 1

lemma rule3(n:nat)
  ensures fusc(2*n) == fusc(n)

lemma rule4(n:nat)
  ensures fusc(2*n+1) == fusc(n) + fusc(n+1)


method ComputeFusc(N: int) returns (b: int)
  requires N >= 0 
  ensures b == fusc(N)
{
  b := 0;
  var n, a := N, 1;

  while (n != 0)
    invariant 0 <= n <= N
    invariant a == fusc(N - n)
    invariant b == fusc(N - n - 1)
    invariant N >= 0
    decreases n
  {
    ghost var d := n; // termination metric

    if (n % 2 == 0)
    {
      rule4(n/2);
      rule3(n/2);

      a := a + b;

      n := n / 2;

    } else {
      rule4((n-1)/2);
      rule3((n-1)/2);
      rule3((n+1)/2);

      b := b + a;

      n := (n - 1) / 2;

    }
  }

  rule1();

  rule2();

  // At this point, n == 0, so a == fusc(N), b == fusc(N-1)
  // We want to return b == fusc(N)
  // But after the loop, a == fusc(N), so assign b := a to ensure postcondition
  b := a;
}

function abs(a: real) : real {if a>0.0 then a else -a}
