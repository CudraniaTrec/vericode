method Abs(x: int) returns (y: int)
	requires x < 0
	ensures 0 < y
	ensures y == -x
{
	// x < 0, so -x > 0
	assert x < 0;
	assert -x > 0;
	y := -x;
	assert 0 < y;
	assert y == -x;
	return y;
}

method Main()
{
	var a := Abs(-3);
	assert a == 3;
}
function abs(a: real) : real {if a>0.0 then a else -a}
