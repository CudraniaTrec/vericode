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

  var prev := 0;
  f := 1;
  var i := 1;

  while i < n
    invariant 1 <= i <= n
    invariant f == Fibonacci(i)
    invariant prev == Fibonacci(i - 1)
  {
    var tmp := f;
    f := f + prev;
    prev := tmp;
    i := i + 1;
    assert f == Fibonacci(i);
    assert prev == Fibonacci(i - 1);
  }
  assert f == Fibonacci(n);
}
function abs(a: real) : real {if a>0.0 then a else -a}
