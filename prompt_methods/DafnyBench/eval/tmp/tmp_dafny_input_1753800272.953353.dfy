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
        assert a - 2 >= 0;
        EvenSquare(a - 2);
        assert IsEven(a - 2);
        assert 2 * (a - 2) >= 0;
        EvenDouble(a - 2);
        assert (a - 2) * (a - 2) >= 0;
        assert 4 * a - 4 >= 0;
        EvenPlus((a - 2) * (a - 2), 4 * a - 4);
    }
}

lemma EvenDouble(a: int)
    requires a >= 0
    ensures IsEven(a + a)
    decreases a
{
    if a == 0 {
        assert IsEven(0 + 0);
    } else if a == 1 {
        assert IsEven(1 + 1);
    } else {
        assert a - 2 >= 0;
        EvenDouble(a - 2);
        // (a + a) = ((a - 2) + (a - 2)) + 4
        EvenPlus((a - 2) + (a - 2), 4);
    }
}

lemma {:induction x} EvenPlus(x: int, y: int)
    requires x >= 0
    requires y >= 0
    requires IsEven(x)
    requires IsEven(y)
    ensures IsEven(x + y)
    decreases x
{
    if x == 0 {
        assert IsEven(0 + y);
        assert IsEven(y);
    } else if x == 1 {
        // impossible, since IsEven(1) == false
        assert false;
    } else {
        assert x - 2 >= 0;
        assert IsEven(x - 2);
        EvenPlus(x - 2, y);
        // (x + y) = ((x - 2) + y) + 2
        EvenPlus((x - 2) + y, 2);
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
