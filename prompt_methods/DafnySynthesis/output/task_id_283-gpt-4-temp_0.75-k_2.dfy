method DigitFrequencyCheck(n: int) returns (ok: bool)
{
    var absN := if n < 0 then -n else n;
    var digits := new int[10];
    var temp := absN;
    if temp == 0 {
        digits[0] := 1;
    } else {
        while temp > 0
            invariant temp >= 0
            invariant forall i :: 0 <= i < 10 ==> digits[i] >= 0
        {
            var d := temp % 10;
            digits[d] := digits[d] + 1;
            temp := temp / 10;
        }
    }
    ok := true;
    var i := 0;
    while i < 10
        invariant 0 <= i <= 10
        invariant ok ==> forall j :: 0 <= j < i ==> digits[j] <= j
    {
        if digits[i] > i {
            ok := false;
            break;
        }
        i := i + 1;
    }
}