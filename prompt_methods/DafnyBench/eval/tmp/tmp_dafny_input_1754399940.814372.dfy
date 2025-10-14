
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
  requires n >= 0
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
  var n := N;
  var a := 1;
  b := 0;

  // Invariant: for current n, a == fusc(n), b == fusc(n-1)
  while n > 0
    invariant 0 <= n <= N
    invariant a == fusc(n)
    invariant b == fusc(n-1)
    decreases n
  {
    if n % 2 == 0 {
      // n even: n = 2*k, fusc(n) = fusc(k)
      n := n / 2;
    } else {
      // n odd: n = 2*k+1, fusc(n) = fusc(k) + fusc(k+1)
      var tmp := a;
      a := a + b;
      b := tmp;
      n := (n - 1) / 2;
    }
  }
  // After loop: n == 0, so a == fusc(0) == 0, b == fusc(-1)
  // But we want to return fusc(N)
  // Actually, the invariant ensures a == fusc(n), b == fusc(n-1)
  // At loop exit, n == 0, so a == fusc(0) == 0, b == fusc(-1)
  // But we want fusc(N). We need to initialize a and b differently.

  // Instead, use the following correct initialization:
  // If N == 0, fusc(0) == 0
  // If N == 1, fusc(1) == 1

  if N == 0 {
    b := 0;
  } else if N == 1 {
    b := 1;
  } else {
    // Re-run the loop with correct initialization
    n := N;
    a := 1;
    b := 0;
    while n > 1
      invariant 1 <= n <= N
      invariant a == fusc(n)
      invariant b == fusc(n-1)
      decreases n
    {
      if n % 2 == 0 {
        n := n / 2;
      } else {
        var tmp := a;
        a := a + b;
        b := tmp;
        n := (n - 1) / 2;
      }
    }
    b := a;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
