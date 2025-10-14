method CountPairsWithEvenXor(a: array<int>) returns (count: int)
    requires a != null
    ensures 0 <= count <= a.Length * (a.Length - 1) / 2
{
    var n := a.Length;
    count := 0;
    var even_count := 0;
    var odd_count := 0;

    // Count even and odd numbers in the array
    for i := 0 to n-1 {
        if a[i] % 2 == 0 {
            even_count := even_count + 1;
        } else {
            odd_count := odd_count + 1;
        }
    }

    // Number of pairs of even numbers: C(even_count, 2)
    // Number of pairs of odd numbers: C(odd_count, 2)
    count := (even_count * (even_count - 1)) / 2 + (odd_count * (odd_count - 1)) / 2;
}