
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
  decreases n
{
  if n == 0 then 0
  else if n == 1 then 1
  else if n % 2 == 0 then fusc(n / 2)
  else fusc((n - 1) / 2) + fusc((n + 1) / 2)
}

lemma rule1()
  ensures fusc(0) == 0
{
}

lemma rule2()
  ensures fusc(1) == 1
{
}

lemma rule3(n:nat)
  ensures fusc(2*n) == fusc(n)
{
}

lemma rule4(n:nat)
  ensures fusc(2*n+1) == fusc(n) + fusc(n+1)
{
}


method ComputeFusc(N: int) returns (b: int)
  requires N >= 0 
  ensures b == fusc(N)
{
  b := 0;
  var n := N;
  var a := 1;

  // Invariant: for current n, a == fusc(n), b == fusc(n-1)
  while (n > 1)
    invariant 0 <= n <= N
    invariant a == fusc(n)
    invariant b == fusc(n-1)
    decreases n
  {
    ghost var d := n; // termination metric

    if (n % 2 == 0)
    {
      // n even: n = 2*k, fusc(n) = fusc(k)
      n := n / 2;
      var tmp := a;
      a := a + b;
      b := tmp;
    } else {
      // n odd: n = 2*k+1, fusc(n) = fusc(k) + fusc(k+1)
      n := (n - 1) / 2;
      var tmp := b;
      b := a + b;
      a := tmp;
    }
  }

  if n == 0 {
    b := 0;
  } else {
    b := a;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
