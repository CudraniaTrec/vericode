
// successfully verifies
method GetEven(a: array<nat>)
requires true;
ensures forall i:int :: 0<=i<a.Length ==> a[i] % 2 == 0
modifies a
{
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j:int :: 0 <= j < i ==> a[j] % 2 == 0
        invariant forall j:int :: i <= j < a.Length ==> a[j] >= 0
    {
        if a[i] % 2 != 0
        {
            a[i] := a[i] + 1;
            assert a[i] % 2 == 0;
        }
        i := i + 1;
    }
    assert forall j:int :: 0 <= j < a.Length ==> a[j] % 2 == 0;
}

function abs(a: real) : real {if a>0.0 then a else -a}
