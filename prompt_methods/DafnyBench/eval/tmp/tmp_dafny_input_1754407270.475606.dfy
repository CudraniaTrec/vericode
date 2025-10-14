
method ContainsSequence(list: seq<seq<int>>, sub: seq<int>) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i < |list| && sub == list[i])
{
    result := false;
    var i: int := 0;
    // Loop invariant: for all j in 0..i, result <==> (exists k :: 0 <= k < i && sub == list[k])
    // Loop invariant: 0 <= i <= |list|
    // Loop invariant: if result, then exists k :: 0 <= k < i && sub == list[k]
    // Loop invariant: if not result, then forall k :: 0 <= k < i ==> sub != list[k]
    while i < |list|
        invariant 0 <= i <= |list|
        invariant result <==> (exists k :: 0 <= k < i && sub == list[k])
        invariant forall k :: 0 <= k < i ==> sub != list[k] ==> !result
    {
        if sub == list[i] {
            result := true;
            break;
        }
        i := i + 1;
    }
    // After the loop: i == |list| || result
    // assert result <==> (exists k :: 0 <= k < i && sub == list[k]);
    // If result is false, then sub != list[k] for all k in 0..|list|-1
    // If result is true, then sub == list[k] for some k in 0..i-1
    // So, result <==> (exists k :: 0 <= k < |list| && sub == list[k])
}

function abs(a: real) : real {if a>0.0 then a else -a}
