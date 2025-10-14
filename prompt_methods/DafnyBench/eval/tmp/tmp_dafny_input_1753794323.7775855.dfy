
method add_small_numbers (a: array<int>, n: int, max: int) returns (r: int)
	requires n > 0;
    requires n <= a.Length;
	requires (forall i: int :: 0 <= i && i < n ==> a[i] <= max);
	ensures r <= max * n;
{
	var i: int;	

	i := 0;
	r := 0;

	while (i < n)
		invariant 0 <= i <= n;
		invariant r == (if i == 0 then 0 else (sum j: int | 0 <= j < i :: a[j]));
		invariant (forall j: int :: 0 <= j < i ==> a[j] <= max);
		invariant r <= max * i;
	{
		r := r + a[i];
		assert a[i] <= max;
		assert r <= max * i + max;
		i := i + 1;
	}
}

function abs(a: real) : real {if a>0.0 then a else -a}
