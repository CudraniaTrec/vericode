
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
    invariant a >= 0
    invariant b >= 0
    invariant a * fusc(n) + b == fusc(n + a * 0 + b * 0) // always a * fusc(n) + b == fusc(n + 0)
    invariant a == 1 ==> b == fusc(N - n)
    decreases n
  {
    ghost var d := n; // termination metric

    if (n % 2 == 0)
    {
      rule4(n/2);
      rule3(n/2);

      // n even, n = 2*k
      // fusc(n) = fusc(2*k) = fusc(k)
      // After: a := a + b; n := n/2;
      a := a + b;
      n := n / 2;
    } else {
      rule4((n-1)/2);
      rule3((n-1)/2);
      rule3((n+1)/2);

      // n odd, n = 2*k+1
      // fusc(n) = fusc(k) + fusc(k+1)
      // After: b := b + a; n := (n-1)/2;
      b := b + a;
      n := (n - 1) / 2;
    }
  }

  rule1();
  rule2();

  // At loop exit: n == 0, so a * fusc(0) + b == fusc(N)
  // fusc(0) == 0, so b == fusc(N)
  assert n == 0;
  assert a * fusc(0) + b == fusc(N);
  assert fusc(0) == 0;
  assert b == fusc(N);

}

function abs(a: real) : real {if a>0.0 then a else -a}
