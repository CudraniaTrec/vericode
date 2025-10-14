
predicate IsOdd(x: int)
{
    x % 2 != 0
}

method FindFirstOdd(a: array<int>) returns (found: bool, index: int)
    requires a != null
    ensures !found ==> forall i :: 0 <= i < a.Length ==> !IsOdd(a[i])
    ensures found ==> 0 <= index < a.Length && IsOdd(a[index]) && forall i :: 0 <= i < index ==> !IsOdd(a[i])
{
    found := false;
    index := 0;
    while (index < a.Length)
        invariant 0 <= index <= a.Length
        invariant !found
        invariant forall i :: 0 <= i < index ==> !IsOdd(a[i])
    {
        if IsOdd(a[index])
        {
            found := true;
            // assert 0 <= index < a.Length;
            // assert IsOdd(a[index]);
            // assert forall i :: 0 <= i < index ==> !IsOdd(a[i]);
            return;
        }
        index := index + 1;
    }
    // assert index == a.Length;
    // assert forall i :: 0 <= i < a.Length ==> !IsOdd(a[i]);
}

function abs(a: real) : real {if a>0.0 then a else -a}
