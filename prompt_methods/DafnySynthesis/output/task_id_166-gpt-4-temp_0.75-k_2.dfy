method CountEvenXorPairs(a: array<int>) returns (count: int)
    requires a != null
    ensures 0 <= count <= a.Length * (a.Length - 1) / 2
    ensures forall i, j :: 0 <= i < j < a.Length ==> (((a[i] ^ a[j]) % 2 == 0) <==> (exists k :: count == k && k == old(count) + 1 && i != j && (a[i] ^ a[j]) % 2 == 0))
{
    var n := a.Length;
    var num_even := 0;
    var num_odd := 0;
    // Count number of even and odd elements
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant 0 <= num_even <= i
        invariant 0 <= num_odd <= i
        invariant num_even + num_odd == i
    {
        if a[i] % 2 == 0 {
            num_even := num_even + 1;
        } else {
            num_odd := num_odd + 1;
        }
        i := i + 1;
    }
    // Number of pairs with xor even: both even or both odd
    count := num_even * (num_even - 1) / 2 + num_odd * (num_odd - 1) / 2;
}