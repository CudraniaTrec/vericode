method Max(a: int, b: int) returns (c: int)
	ensures c >= a && c >= b && (c == a || c == b)
{
	// Strongest possible assertions before branching
	assert true;
	if (a >= b)
	{
		assert a >= b;
		assert a >= a && a >= b && (a == a || a == b);
		return a;
	} else {
		assert b > a;
		assert b >= a && b >= b && (b == a || b == b);
		return b;
	}
}

method Main()
{
	print "Testing max...\n";

	var max := Max(3, 4);
	assert max == 4;

	max := Max(-3, 4);
	assert max == 4;

	max := Max(-3, -4);
	assert max == -3;

	max := Max(5555555, 5555);
	assert max == 5555555;
}
function abs(a: real) : real {if a>0.0 then a else -a}
