//Dafny Code

method Power(a: int, b: nat) returns (result: int)
    requires b >= 0
    ensures result == a ^ b
{
    var res := 1;
    var base := a;
    var exp := b;
    while exp > 0
        invariant exp >= 0
        invariant res * base ^ exp == a ^ b
    {
        if exp % 2 == 1 {
            res := res * base;
        }
        base := base * base;
        exp := exp / 2;
    }
    result := res;
}