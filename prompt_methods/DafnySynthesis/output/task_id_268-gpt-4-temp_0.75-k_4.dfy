//Dafny Code

method StarNumber(n: nat) returns (star: nat)
    ensures star == 6 * n * (n - 1) / 2 + 1
{
    if n == 0 {
        star := 0;
    } else {
        star := 6 * n * (n - 1) / 2 + 1;
    }
}