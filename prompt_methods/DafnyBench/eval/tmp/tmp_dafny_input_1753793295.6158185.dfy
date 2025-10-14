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
        decreases |a| - i
    {
        if a[i] <= b[i]
        {
            result := false;
            // At this point, i < |a| and a[i] <= b[i]
            // So the invariant !result ==> exists j :: 0 <= j < i && a[j] <= b[j] holds for j == i
            break;
        }
        i := i + 1;
    }
    // After the loop: either i == |a| (no break), or result == false and loop exited early
    if result {
        // We checked all indices, and all a[j] > b[j]
        assert forall j :: 0 <= j < |a| ==> a[j] > b[j];
    } else {
        // There exists some j < |a| with a[j] <= b[j]
        assert exists j :: 0 <= j < |a| && a[j] <= b[j];
    }
}
function abs(a: real) : real {if a>0.0 then a else -a}
