
method ContainsConsecutiveNumbers(a: array<int>) returns (result: bool)
    requires a.Length>0
    ensures result <==> (exists i :: 0 <= i < a.Length - 1 && a[i] + 1 == a[i + 1])
{
    result := false;
    var found: bool := false;
    var idx: int := -1;
    // The loop only makes sense for i in 0 .. a.Length-2
    // So we adjust the loop accordingly
    var i: int := 0;
    while i < a.Length - 1
        invariant 0 <= i <= a.Length - 1
        invariant !result ==> (forall j :: 0 <= j < i ==> a[j] + 1 != a[j + 1])
        invariant result ==> (exists j :: 0 <= j < i && a[j] + 1 == a[j + 1])
    {
        if a[i] + 1 == a[i + 1] {
            result := true;
            // At this point, result is true, so the postcondition will be satisfied
            break;
        }
        i := i + 1;
    }
    // After the loop, either result is true and the postcondition is satisfied,
    // or result is false and we have checked all possible i.
    assert result <==> (exists j :: 0 <= j < a.Length - 1 && a[j] + 1 == a[j + 1]);
}

function abs(a: real) : real {if a>0.0 then a else -a}
