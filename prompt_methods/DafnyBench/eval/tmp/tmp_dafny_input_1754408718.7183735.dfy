method Abs(x: int) returns (y: int)
	requires x < 0
	ensures 0 < y
	ensures y == -x
{
	// x < 0
	assert x < 0;
	// -x > 0
	assert -x > 0;
	// y == -x
	return -x;
}

method Main()
{
	var a := Abs(-3);
	// a == 3
	assert a == 3;
}

function abs(a: real) : real {if a>0.0 then a else -a}
