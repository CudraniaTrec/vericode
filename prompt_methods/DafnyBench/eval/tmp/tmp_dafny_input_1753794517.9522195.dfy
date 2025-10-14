
method mult(a:int, b:int) returns (x:int)
  	requires a >= 0 && b >= 0
  	ensures x == a * b
{
  	x := 0;
	var y := a;
  	while y > 0
		invariant 0 <= y <= a
		invariant x == (a - y) * b
		invariant a >= 0 && b >= 0
	{
		x := x + b;
		y := y - 1;
		assert x == (a - y) * b;
	}
	assert y == 0;
	assert x == (a - 0) * b;
}

function abs(a: real) : real {if a>0.0 then a else -a}
