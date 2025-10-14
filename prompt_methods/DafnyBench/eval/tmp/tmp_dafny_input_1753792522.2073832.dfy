
method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
    ensures true <== (exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|])
{
    if |sub| > |main| {
        return false;
    }

    var found := false;
    // Invariant: found == (exists j :: 0 <= j < i && sub == main[j..j+|sub|])
    for i := 0 to |main| - |sub| + 1
        invariant 0 <= i <= |main| - |sub| + 1
        invariant found == (exists j :: 0 <= j < i && sub == main[j..j+|sub|])
    {
        if sub == main[i..i + |sub|] {
            found := true;
        }
    }
    result := found;
    assert result == (exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|]);
}

function abs(a: real) : real {if a>0.0 then a else -a}
