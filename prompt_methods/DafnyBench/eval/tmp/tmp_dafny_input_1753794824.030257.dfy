
method Abs(x: int) returns (y: int)
	requires x == -1
	ensures 0 <= y
	ensures 0 <= x ==> y == x
	ensures x < 0 ==> y == -x
{
	// x == -1 by precondition
	assert x == -1;
	y := x + 2;
	assert y == 1;
	assert 0 <= y;
	assert !(0 <= x); // x == -1 < 0
	assert y == -x;
	return y;
}

method Abs2(x: real) returns (y: real)
	requires x == -0.5
	ensures 0.0 <= y
	ensures 0.0 <= x ==> y == x
	ensures x < 0.0 ==> y == -x
{
	// x == -0.5 by precondition
	assert x == -0.5;
	y := x + 1.0;
	assert y == 0.5;
	assert 0.0 <= y;
	assert !(0.0 <= x); // x == -0.5 < 0.0
	assert y == -x;
	return y;
}

method Main()
{
	var a := Abs(-1);
	var a2 := Abs2(-0.5);
}

function abs(a: real) : real {if a>0.0 then a else -a}
