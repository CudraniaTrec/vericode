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
            assert sub == list[i];
            assert exists j :: 0 <= j < i+1 && sub == list[j];
            break;
        }
        i := i + 1;
    }
    assert result <==> (exists j :: 0 <= j < i && sub == list[j]);
    // After the loop, i == |list| if we didn't break
    if !result {
        assert i == |list|;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
