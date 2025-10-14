method main(x: int, y: int) returns (x_out: int, y_out: int, n: int)
requires x >= 0
requires y >= 0
requires x == y
ensures y_out == n
{
    x_out := x;
    y_out := y;
    n := 0;

    while (x_out != n)
        invariant x_out >= 0
        invariant y_out >= 0
        invariant x_out == y_out
        invariant x_out + n == x
        invariant y_out + n == y
        invariant n == 0
    {
        x_out := x_out - 1;
        y_out := y_out - 1;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
