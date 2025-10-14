predicate IsEven(n: int)
{
    n % 2 == 0
}

method IsProductEven(a: array<int>) returns (result: bool)
    ensures result <==> exists i :: 0 <= i < a.Length && IsEven(a[i])
{
    result := false;
    var found := false;
    var idx := 0;
    while idx < a.Length
        invariant 0 <= idx <= a.Length
        invariant !result ==> forall j :: 0 <= j < idx ==> !IsEven(a[j])
        invariant result ==> exists j :: 0 <= j < idx && IsEven(a[j])
    {
        if IsEven(a[idx])
        {
            result := true;
            // assert exists j :: 0 <= j <= idx && IsEven(a[j]);
            break;
        }
        idx := idx + 1;
    }
    // assert result <==> exists i :: 0 <= i < a.Length && IsEven(a[i]);
}
function abs(a: real) : real {if a>0.0 then a else -a}
