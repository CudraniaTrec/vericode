
method Main() returns (x: int, y: int)
	ensures x == y;
{
	x := 0;
	y := 0;
	var w := 1;
	var z := 0;
	var turn := 0;

	while(x != y)
		invariant 0 <= x
		invariant 0 <= y
		invariant x >= 0 && y >= 0
		invariant turn == 0 || turn == 1 || turn == 2
		invariant w == z + 1 || turn == 0 || turn == 1
		invariant x - y == 0 || x - y == 1 || x - y == -1
		invariant (turn == 1 ==> (x == y || x == y + 1 || x + 1 == y))
		invariant (turn == 2 ==> (z >= 0 && w == z + 1))
		invariant (turn == 0 ==> (w == z + 1))
		invariant x >= y
	{
		if(turn == 0){
			turn := 1;
			assert turn == 1;
		}

		if(turn == 1){
			if(w % 2 == 1){
				x := x + 1;
				assert x >= y;
			}

			if(z % 2 == 0){
				y := y + 1;
				assert x >= y;
			}

			turn := 1;
			assert turn == 1;
		}
		else{
			if(turn == 2){
				z := z + y;
				w := z + 1;
				assert w == z + 1;

				turn := 0;
				assert turn == 0;
			}
		}
	}
	assert x == y;
}

function abs(a: real) : real {if a>0.0 then a else -a}
