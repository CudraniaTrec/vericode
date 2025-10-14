method intersperse(numbers: seq<int>, delimiter: int) returns (interspersed: seq<int>)
    ensures |interspersed| == if |numbers| > 0 then 2 * |numbers| - 1 else 0
    ensures forall i :: 0 <= i < |interspersed| ==> i % 2 == 0 ==> 
                interspersed[i] == numbers[i / 2]
    ensures forall i :: 0 <= i < |interspersed| ==> i % 2 == 1 ==>
                interspersed[i] == delimiter
{
    interspersed := [];
    var n := |numbers|;
    // Loop invariants:
    // - 0 <= i <= n
    // - |interspersed| == if i == 0 then 0 else 2 * i - 1
    // - forall j :: 0 <= j < |interspersed| ==>
    //       (j % 2 == 0 ==> interspersed[j] == numbers[j / 2]) &&
    //       (j % 2 == 1 ==> interspersed[j] == delimiter)
    for i := 0 to n
        invariant 0 <= i <= n
        invariant |interspersed| == (if i == 0 then 0 else 2 * i - 1)
        invariant forall j :: 0 <= j < |interspersed| ==>
            (j % 2 == 0 ==> interspersed[j] == numbers[j / 2]) &&
            (j % 2 == 1 ==> interspersed[j] == delimiter)
    {
        if i > 0 {
            interspersed := interspersed + [delimiter];
        }
        if i < n {
            interspersed := interspersed + [numbers[i]];
        }
    }
}
function abs(a: real) : real {if a>0.0 then a else -a}
