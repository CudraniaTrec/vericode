// Dafny Code

method BellNumber(n: nat) returns (b: nat)
    ensures b == bell(n)
{
    var bellNumbers := new nat[n+1];
    bellNumbers[0] := 1;
    var i := 1;
    while i <= n
        invariant 0 <= i <= n+1
        invariant bellNumbers[0..i] == [bell(j) | j : int :: 0 <= j < i]
    {
        var temp := new nat[i+1];
        temp[0] := bellNumbers[i-1];
        var j := 1;
        while j <= i
            invariant 1 <= j <= i+1
        {
            temp[j] := temp[j-1] + bellNumbers[i-j];
            j := j + 1;
        }
        bellNumbers[i] := temp[i];
        i := i + 1;
    }
    b := bellNumbers[n];
}

/// Helper function: Mathematical Bell number definition
function bell(n: nat): nat
    decreases n
{
    if n == 0 then 1
    else (sum k | 0 <= k < n :: binomial(n-1, k) * bell(k))
}

/// Binomial coefficient function
function binomial(n: nat, k: nat): nat
{
    if k > n then 0
    else if k == 0 || k == n then 1
    else binomial(n-1, k-1) + binomial(n-1, k)
}