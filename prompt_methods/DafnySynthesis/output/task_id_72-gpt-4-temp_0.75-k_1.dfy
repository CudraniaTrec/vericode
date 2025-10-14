// Dafny Code

method CanBeWrittenAsDifferenceOfSquares(n: int) returns (res: bool)
{
    // A number n can be written as a^2 - b^2 = (a-b)(a+b)
    // So, n is the product of two integers of the same parity (both odd or both even)
    // All odd numbers can be expressed as a difference of two squares.
    // All multiples of 4 can also be expressed as a difference of two squares.
    // But numbers of the form 4k+2 (i.e., n % 4 == 2) CANNOT be expressed as a difference of two squares.
    // Negative numbers can also be represented, e.g., 1^2 - 2^2 = -3
    // We'll allow any integer n

    if n == 0 {
        // 0 = 1^2 - 1^2, so it's possible
        res := true;
    } else if n % 4 == 2 || n % 4 == -2 {
        // Numbers congruent to 2 mod 4 cannot be represented
        res := false;
    } else {
        res := true;
    }
}