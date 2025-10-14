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
            // At this point: i < |a|, a[i] <= b[i]
            // So: exists j :: 0 <= j < i+1 && a[j] <= b[j]
            // Invariant for !result holds for i+1
            break;
        }
        i := i + 1;
    }
    // After the loop:
    // If result is true, then for all j < i, a[j] > b[j], and i == |a| (since only break sets result := false)
    // If result is false, then there exists j < i+1 with a[j] <= b[j], and i < |a| (since break)
    if result {
        assert i == |a|;
        assert forall j :: 0 <= j < |a| ==> a[j] > b[j];
    } else {
        assert exists j :: 0 <= j < |a| && a[j] <= b[j];
    }
}
function abs(a: real) : real {if a>0.0 then a else -a}
