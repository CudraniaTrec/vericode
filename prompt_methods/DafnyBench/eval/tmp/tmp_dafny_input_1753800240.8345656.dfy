
// RUN: /compile:0 /nologo

function IsEven(a : int) : bool
    requires a >= 0
{
    if a == 0 then      true 
    else if a == 1 then false 
    else                IsEven(a - 2)
}

lemma EvenSquare(a : int)
requires a >= 0
ensures IsEven(a) ==> IsEven(a * a)
{
    if a >= 2 && IsEven(a) {
        // a >= 2 && IsEven(a)
        assert a - 2 >= 0;
        assert IsEven(a - 2);
        EvenSquare(a - 2);
        // 2*a - 2 >= 0
        assert 2 * a - 2 >= 0;
        EvenDouble(a - 2);
        EvenDouble(a);
        // (a - 2) * (a - 2) >= 0
        assert (a - 2) * (a - 2) >= 0;
        // 4*a - 4 >= 0
        assert 4 * a - 4 >= 0;
        EvenPlus((a - 2) * (a - 2), 4 * a - 4);
    }
}

lemma EvenDouble(a: int)
    requires a >= 0
    ensures IsEven(a + a)
{
    var i := a;
    while i >= 2
        invariant 0 <= i <= a
        invariant IsEven((a - i) + (a - i))
        decreases i
    {
        i := i - 2;
    }
    assert i == 0 || i == 1;
    if i == 0 {
        assert IsEven(a + a);
    } else {
        assert i == 1;
        assert !IsEven(a + a); // unreachable since a >= 0 and a even
    }
    if a >= 2 {
        assert a - 2 >= 0;
        EvenDouble(a - 2);
    }
}

lemma {:induction x} EvenPlus(x: int, y: int)
    requires x >= 0
    requires y >= 0
    requires IsEven(x)
    requires IsEven(y)
    ensures IsEven(x + y)
{
    var i := x;
    while i >= 2
        invariant 0 <= i <= x
        invariant IsEven(i)
        invariant IsEven(y)
        invariant IsEven((x - i) + y)
        decreases i
    {
        i := i - 2;
    }
    assert i == 0 || i == 1;
    if i == 0 {
        assert IsEven(0 + y);
        assert IsEven(y);
    } else {
        assert i == 1;
        // unreachable since IsEven(i) and i == 1
        assert false;
    }
    if x >= 2 {
        assert x - 2 >= 0;
        assert IsEven(x - 2);
        EvenPlus(x - 2, y);
    }
}


/*
lemma {:induction x} EvenTimes(x: int, y: int)
    requires x >= 0
    requires y >= 0
    requires IsEven(x)
    requires IsEven(y)
    ensures IsEven(x * y)
{
    if x >= 2 {
        calc {
            IsEven(x * y);
            IsEven((x - 2) * y + 2 * y); { Check1(y); EvenPlus((x - 2) * y, 2 * y); }
            true;
        }
    }
}
*/

function abs(a: real) : real {if a>0.0 then a else -a}
