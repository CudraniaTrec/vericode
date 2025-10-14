
method F() returns ( r: int)
    ensures r <= 0
{
    r := 0;
}

method Main() 
{
    var x := F();
    x := x-1;
    print x;
}


method Mid( p: int, q: int) returns ( m: int )
    // | ... | ??? | ... |
    //        p m   q
    requires p <= q;
    ensures p<= m <= q;
    ensures m-p <= q-m;
    ensures 0 <= (q-m)-(m-p) <= 1;

{
    // strongest annotation: p <= q
    assert p <= q;
    m := (p+q)/2;
    // strongest annotation: p <= m <= q
    assert p <= m <= q;
    // strongest annotation: m-p <= q-m
    assert m-p <= q-m;
    // strongest annotation: 0 <= (q-m)-(m-p) <= 1
    assert 0 <= (q-m)-(m-p) <= 1;
}

function abs(a: real) : real {if a>0.0 then a else -a}
