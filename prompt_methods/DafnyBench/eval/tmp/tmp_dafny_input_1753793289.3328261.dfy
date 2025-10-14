method IsSmaller(a: seq<int>, b: seq<int>) returns (result: bool)
    requires |a| == |b|
    ensures result <==> forall i :: 0 <= i < |a| ==> a[i] > b[i]
    ensures !result <==> exists i :: 0 <= i < |a| && a[i] <= b[i]
{
    result := true;
    var i: int := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant result ==> forall j :: 0 <= j < i ==> a[j] > b[j]
        invariant !result ==> exists j :: 0 <= j < i && a[j] <= b[j]
    {
        if a[i] <= b[i]
        {
            result := false;
            break;
        }
        i := i + 1;
    }
    assert result ==> forall j :: 0 <= j < i ==> a[j] > b[j];
    assert !result ==> exists j :: 0 <= j < i && a[j] <= b[j];
    assert i == |a| || !result;
    assert result ==> forall j :: 0 <= j < |a| ==> a[j] > b[j];
    assert !result ==> exists j :: 0 <= j < |a| && a[j] <= b[j];
}
function abs(a: real) : real {if a>0.0 then a else -a}
