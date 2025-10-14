
// definition of Fibonacci numbers
function Fibonacci(n: nat): nat {
  match n {
    case 0 => 0
    case 1 => 1
    case _ => Fibonacci(n - 1) + Fibonacci(n - 2)
  }
}

// iterative calculation of Fibonacci numbers
method FibonacciIterative(n: nat) returns (f: nat)
  ensures f == Fibonacci(n)
{
  if n < 2 {
    return n;
  }

  var prev := 1;
  f := 1;
  var i := 2;

  while i < n
    invariant 2 <= i <= n
    invariant f == Fibonacci(i - 1)
    invariant prev == Fibonacci(i - 2)
  {
    prev, f := f, f + prev;
    i := i + 1;
    assert f == Fibonacci(i - 1);
    assert prev == Fibonacci(i - 2);
  }
  assert f == Fibonacci(n - 1);
  assert prev == Fibonacci(n - 2);
  // After the loop, i == n
  // So f == Fibonacci(n - 1), prev == Fibonacci(n - 2)
  // But we want to return Fibonacci(n)
  f := f + prev;
  assert f == Fibonacci(n);
}

function abs(a: real) : real {if a>0.0 then a else -a}
