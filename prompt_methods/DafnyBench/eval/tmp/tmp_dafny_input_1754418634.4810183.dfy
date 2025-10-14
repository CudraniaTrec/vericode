
method Eval(x:int) returns (r:int)		// do not change
requires x >= 0
ensures r == x*x
{ 										// do not change
var y:int := x; 						// do not change
var z:int := 0; 						// do not change
while y>0 								// do not change
    invariant 0 <= y <= x
    invariant z == x * (x - y)
    invariant x >= 0
{ 										// do not change
z := z + x; 							// do not change
y := y - 1; 							// do not change
} 										// do not change
assert y == 0;
assert z == x * (x - y);
assert z == x * x;
return z; 								// do not change
} 										// do not change

function abs(a: real) : real {if a>0.0 then a else -a}
