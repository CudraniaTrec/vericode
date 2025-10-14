//Dafny Code

method SumPerrin(n: nat) returns (sum: nat)
    requires n >= 0
    ensures sum == (if n == 0 then 3
                    else if n == 1 then 0
                    else if n == 2 then 2
                    else SumPerrin(n-1) + Perrin(n))
{
    var perrin := new int[n+1];
    if n >= 0 { perrin[0] := 3; }
    if n >= 1 { perrin[1] := 0; }
    if n >= 2 { perrin[2] := 2; }
    var i := 3;
    while i <= n
        invariant 3 <= i <= n+1
        invariant forall k :: 0 <= k < 3 ==> perrin[k] == (if k == 0 then 3 else if k == 1 then 0 else 2)
        invariant forall k :: 3 <= k < i ==> perrin[k] == perrin[k-2] + perrin[k-3]
    {
        perrin[i] := perrin[i-2] + perrin[i-3];
        i := i + 1;
    }
    sum := 0;
    var j := 0;
    while j <= n
        invariant 0 <= j <= n+1
        invariant sum == (if j == 0 then 0 else old(sum) + perrin[j-1])
    {
        sum := sum + perrin[j];
        j := j + 1;
    }
}

// Helper function to compute a single Perrin number (not strictly necessary for above code, but useful for ensures)
function Perrin(k: nat): nat
{
    if k == 0 then 3
    else if k == 1 then 0
    else if k == 2 then 2
    else Perrin(k-2) + Perrin(k-3)
}