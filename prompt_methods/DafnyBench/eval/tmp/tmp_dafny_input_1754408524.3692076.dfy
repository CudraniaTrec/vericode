
method UpWhileLess(N: int) returns (i: int)
requires 0 <= N
ensures i == N
{
    i := 0;
    while i < N 
        invariant 0 <= i <= N
        decreases N - i
    {
        i := i + 1;
        assert 0 <= i <= N;
    }
}

method UpWhileNotEqual(N: int) returns (i: int)
requires 0 <= N
ensures i == N
{
    i := 0;
    while i != N
        invariant 0 <= i <= N
        decreases N - i
    {
        i := i + 1;
        assert 0 <= i <= N;
    }
}

method DownWhileNotEqual(N: int) returns (i: int)
requires 0 <= N
ensures i == 0
{
    i := N;
    while i != 0 
        invariant 0 <= i <= N
        decreases i
    {
        i := i - 1;
        assert 0 <= i <= N;
    }
}

method DownWhileGreater(N: int) returns (i: int)
requires 0 <= N
ensures i == 0
{
    i := N;
    while 0 < i 
        invariant 0 <= i <= N
        decreases i
    {
        i := i - 1;
        assert 0 <= i <= N;
    }
}

method Quotient()
{
    var x, y := 0, 191;
    while 7 <= y
        invariant 0 <= x
        invariant 0 <= y < 191 - 7 * x + 1
        invariant 191 == 7 * x + y
        decreases y
    {
        y := y - 7;
        x := x + 1;
        assert 191 == 7 * x + y;
        assert 0 <= x;
        assert 0 <= y;
    }
}

method Quotient1() 
{
    var x, y := 0, 191;
    while 7 <= y
        invariant 0 <= x
        invariant 0 <= y
        decreases y
    {
        x, y := 27, 2;
        assert x == 27 && y == 2;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
