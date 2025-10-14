
method intersperse(numbers: seq<int>, delimiter: int) returns (interspersed: seq<int>)
    ensures |interspersed| == if |numbers| > 0 then 2 * |numbers| - 1 else 0
    ensures forall i :: 0 <= i < |interspersed| ==> i % 2 == 0 ==> 
                interspersed[i] == numbers[i / 2]
    ensures forall i :: 0 <= i < |interspersed| ==> i % 2 == 1 ==>
                interspersed[i] == delimiter
{
    interspersed := [];
    var n := |numbers|;
    // Loop invariant: 
    //  - 0 <= i <= n
    //  - |interspersed| == if i > 0 then 2 * i - 1 else 0
    //  - forall j :: 0 <= j < |interspersed| ==> 
    //        (j % 2 == 0 ==> interspersed[j] == numbers[j / 2]) &&
    //        (j % 2 == 1 ==> interspersed[j] == delimiter)
    //  - forall k :: 0 <= k < i ==> numbers[k] == numbers[k]
    //  - interspersed == (if i == 0 then [] else 
    //        [numbers[0]] + ([delimiter, numbers[1]] + ... + [delimiter, numbers[i-1]]))
    for i := 0 to n
        invariant 0 <= i <= n
        invariant |interspersed| == (if i > 0 then 2 * i - 1 else 0)
        invariant forall j :: 0 <= j < |interspersed| ==>
            (j % 2 == 0 ==> interspersed[j] == numbers[j / 2]) &&
            (j % 2 == 1 ==> interspersed[j] == delimiter)
    {
        if i > 0 {
            interspersed := interspersed + [delimiter];
            assert |interspersed| % 2 == 0;
            assert |interspersed| == 2 * i - 2 + 1;
        }
        if i < n {
            interspersed := interspersed + [numbers[i]];
            assert |interspersed| == (if i >= 0 then 2 * (i + 1) - 1 else 0);
            assert interspersed[|interspersed|-1] == numbers[i];
        }
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
