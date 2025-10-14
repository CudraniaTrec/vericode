//Dafny Code

method SumAndAverage(n: nat) returns (sum: nat, avg: real)
    ensures sum == n * (n + 1) / 2
    ensures avg == if n == 0 then 0.0 else sum as real / n
{
    // Using the formula for sum of first n natural numbers
    sum := n * (n + 1) / 2;
    if n == 0 {
        avg := 0.0;
    } else {
        avg := sum as real / n;
    }
}