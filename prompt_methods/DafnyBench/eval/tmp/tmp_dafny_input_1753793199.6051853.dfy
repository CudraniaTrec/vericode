predicate IsEven(n: int)
{
    n % 2 == 0
}

method IsEvenAtIndexEven(lst: seq<int>) returns (result: bool)
    ensures result <==> forall i :: 0 <= i < |lst| ==> (IsEven(i) ==> IsEven(lst[i]))
{
    result := true;
    var i: int := 0;
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant result ==> forall j :: 0 <= j < i ==> (IsEven(j) ==> IsEven(lst[j]))
        invariant !result ==> exists j :: 0 <= j < i && IsEven(j) && !IsEven(lst[j])
    {
        if IsEven(i) && !IsEven(lst[i])
        {
            result := false;
            break;
        }
        i := i + 1;
    }
    assert result <==> forall j :: 0 <= j < i ==> (IsEven(j) ==> IsEven(lst[j]));
    assert i <= |lst|;
    // After the loop: if result is still true, then all checked indices satisfy the property
    // If result is false, then a counterexample was found
    // We need to ensure the postcondition for all indices
}

function abs(a: real) : real {if a>0.0 then a else -a}
