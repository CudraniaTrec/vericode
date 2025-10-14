
method square (n: int) returns (r: int)
	requires 0 <= n;
	ensures r == n*n;
{
	var x: int;
	var i: int;

	r := 0;
	i := 0;
	x := 1;

	while (i < n)
		invariant 0 <= i <= n
		invariant x == 2*i + 1
		invariant r == i*i
	{
		r := r + x;
		x := x + 2;
		i := i + 1;
	}
}

function abs(a: real) : real {if a>0.0 then a else -a}
