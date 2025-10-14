//Dafny Code

method IsNonPrime(n: int) returns (nonPrime: bool)
    ensures nonPrime <==> (n <= 1 || exists k :: 2 <= k < n && n % k == 0)
{
    if n <= 1 {
        nonPrime := true;
        return;
    }
    var found := false;
    var k := 2;
    while k < n
        decreases n - k
    {
        if n % k == 0 {
            found := true;
            break;
        }
        k := k + 1;
    }
    nonPrime := found;
}