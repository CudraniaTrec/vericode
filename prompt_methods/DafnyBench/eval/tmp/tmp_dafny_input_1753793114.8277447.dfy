
predicate IsOdd(n: int)
{
    n % 2 == 1
}

method IsOddAtIndexOdd(a: array<int>) returns (result: bool)
    ensures result <==> forall i :: 0 <= i < a.Length ==> (IsOdd(i) ==> IsOdd(a[i]))
{
    result := true;
    var i: int := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant result ==> forall j :: 0 <= j < i ==> (IsOdd(j) ==> IsOdd(a[j]))
        invariant !result ==> exists j :: 0 <= j < i && IsOdd(j) && !IsOdd(a[j])
    {
        if IsOdd(i) && !IsOdd(a[i])
        {
            result := false;
            break;
        }
        i := i + 1;
    }
    // After the loop, if result is still true, then for all j < i == a.Length, the property holds
    // If result is false, then there exists some j < i where IsOdd(j) && !IsOdd(a[j])
}

function abs(a: real) : real {if a>0.0 then a else -a}
