
method ContainsConsecutiveNumbers(a: array<int>) returns (result: bool)
    requires a.Length>0
    ensures result <==> (exists i :: 0 <= i < a.Length - 1 && a[i] + 1 == a[i + 1])
{
    result := false;
    var found: bool := false;
    var idx: int := -1;
    // The loop only makes sense for i in 0 .. a.Length-2
    // So we loop to a.Length-2
    var N := a.Length;
    var last := N - 1;
    var limit := N - 1;
    // Invariant: result == (exists j :: 0 <= j < i && a[j] + 1 == a[j + 1])
    // Invariant: 0 <= i <= limit + 1
    for i := 0 to limit
        invariant 0 <= i <= limit + 1
        invariant result == (exists j :: 0 <= j < i && a[j] + 1 == a[j + 1])
    {
        if a[i] + 1 == a[i + 1] {
            result := true;
            assert (exists j :: 0 <= j < i+1 && a[j] + 1 == a[j + 1]);
            break;
        }
    }
    // After the loop:
    // result == (exists j :: 0 <= j < i && a[j] + 1 == a[j + 1])
    // If result == false, then no such pair exists in the array
    assert result <==> (exists i :: 0 <= i < a.Length - 1 && a[i] + 1 == a[i + 1]);
}

function abs(a: real) : real {if a>0.0 then a else -a}
