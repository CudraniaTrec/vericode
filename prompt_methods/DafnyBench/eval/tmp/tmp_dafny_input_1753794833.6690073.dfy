function fib(n: nat): nat
{
	if n == 0 then 0 else
	if n == 1 then 1 else
		fib(n - 1) + fib(n - 2)
}

method ComputeFib(n: nat) returns (b: nat)
	ensures b == fib(n)
{
	var i: int := 1;
	if 0 <= n < 2 { return n; }
	b := 1;
	var c := 0;

	// At loop entry: i == 1, b == 1, c == 0
	while i < n
		invariant 1 <= i <= n
		invariant b == fib(i)
		invariant c == fib(i - 1)
		decreases n - i
	{
		b, c := b + c, b;
		i := i + 1;
	}
	assert i == n;
	assert b == fib(n);
}

method Main()
{
	var ret := ComputeFib(5);
}

function abs(a: real) : real {if a>0.0 then a else -a}
