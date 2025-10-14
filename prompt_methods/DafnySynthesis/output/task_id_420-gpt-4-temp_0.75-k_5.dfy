// Dafny Code

method CubeSumOfFirstNEvenNumbers(n: nat) returns (sum: nat)
    ensures sum == (n * (n + 1)) * (n * (n + 1))
{
    // The first n even natural numbers are: 2, 4, 6, ..., 2n
    // The sum of their cubes is: 2^3 + 4^3 + 6^3 + ... + (2n)^3
    // This can be written as: 8*(1^3 + 2^3 + ... + n^3)
    // The sum of the first n cubes: (n(n+1)/2)^2

    var sumOfCubes := 0;
    var i := 1;
    while i <= n
        invariant 1 <= i <= n+1
        invariant sumOfCubes == 8 * (i-1)*(i) / 2 * (i-1)*(i) / 2
    {
        sumOfCubes := sumOfCubes + (2 * i) * (2 * i) * (2 * i);
        i := i + 1;
    }
    sum := sumOfCubes;
}