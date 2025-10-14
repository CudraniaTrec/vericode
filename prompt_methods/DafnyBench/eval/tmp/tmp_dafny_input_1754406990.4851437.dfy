
method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
    ensures true <== (exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|])
{
    if |sub| > |main| {
        return false;
    }

    var found: bool := false;
    var i: int := 0;
    while i <= |main| - |sub| 
        invariant 0 <= i <= |main| - |sub| + 1
        invariant found ==> (exists j :: 0 <= j < i && sub == main[j..j + |sub|])
        invariant !found ==> (forall j :: 0 <= j < i ==> sub != main[j..j + |sub|])
    {
        if sub == main[i..i + |sub|] {
            found := true;
        }
        i := i + 1;
    }
    result := found;
    assert result ==> (exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|]);
}

function abs(a: real) : real {if a>0.0 then a else -a}
