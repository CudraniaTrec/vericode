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
    if result {
        assert forall j :: 0 <= j < |lst| ==> (IsEven(j) ==> IsEven(lst[j]));
    } else {
        // There exists some j < i with IsEven(j) && !IsEven(lst[j])
        // For indices >= i, result is false, so postcondition holds vacuously
        assert exists j :: 0 <= j < i && IsEven(j) && !IsEven(lst[j]);
        assert forall j :: 0 <= j < |lst| ==> (IsEven(j) ==> IsEven(lst[j])) || !result;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
