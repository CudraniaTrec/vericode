predicate IsEven(n: int)
{
    n % 2 == 0
}

method IsProductEven(a: array<int>) returns (result: bool)
    ensures result <==> exists i :: 0 <= i < a.Length && IsEven(a[i])
{
    result := false;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant result ==> (exists j :: 0 <= j < i && IsEven(a[j]))
        invariant !result ==> (forall j :: 0 <= j < i ==> !IsEven(a[j]))
    {
        if IsEven(a[i])
        {
            result := true;
            break;
        }
        i := i + 1;
    }
    // After the loop: either result is true (found), or i == a.Length and result is false
    if !result {
        assert forall k :: 0 <= k < a.Length ==> !IsEven(a[k]);
    } else {
        assert exists k :: 0 <= k < a.Length && IsEven(a[k]);
    }
}
function abs(a: real) : real {if a>0.0 then a else -a}
