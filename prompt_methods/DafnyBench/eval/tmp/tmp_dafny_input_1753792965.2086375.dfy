method ContainsSequence(list: seq<seq<int>>, sub: seq<int>) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i < |list| && sub == list[i])
{
    result := false;
    var i: int := 0;
    while i < |list|
        invariant 0 <= i <= |list|
        invariant !result ==> (forall j :: 0 <= j < i ==> sub != list[j])
        invariant result ==> (exists j :: 0 <= j < i && sub == list[j])
    {
        if sub == list[i] {
            result := true;
            break;
        }
        i := i + 1;
    }
    // After the loop: either result is true and there is some j < i with sub == list[j],
    // or result is false and forall j < i, sub != list[j], and i == |list|
    if result {
        assert exists j :: 0 <= j < i && sub == list[j];
        assert exists j :: 0 <= j < |list| && sub == list[j];
    } else {
        assert i == |list|;
        assert forall j :: 0 <= j < |list| ==> sub != list[j];
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
