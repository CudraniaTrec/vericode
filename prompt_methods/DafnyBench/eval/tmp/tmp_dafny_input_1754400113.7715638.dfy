method M1(x: int, y: int) returns (r: int)
ensures r == x*y
{
    if (x == 0){
        r:= 0;
        assert r == x*y;
    } else if( x < 0){
        r:= M1(-x, y);
        assert r == (-x)*y;
        r:= -r;
        assert r == x*y;
    } else {
        r:= M1(x-1, y);
        assert r == (x-1)*y;
        r:= A1(r, y); 
        assert r == (x-1)*y + y;
        assert r == x*y;
    }
}

method A1(x: int, y: int) returns (r: int)
ensures r == x + y
{
    r:= x;
    if( y < 0){
        var n:= y;
        while(n != 0)
            invariant n <= 0
            invariant r + n == x + y
            decreases -n
        {
            r:= r-1;
            n:= n + 1;
            assert r + n == x + y;
        }
        assert n == 0;
        assert r == x + y;
    } else {
        var n := y;
        while(n!= 0)
            invariant n >= 0
            invariant r + n == x + y
            decreases n
        {
            r:= r + 1;
            n:= n - 1;
            assert r + n == x + y;
        }
        assert n == 0;
        assert r == x + y;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
