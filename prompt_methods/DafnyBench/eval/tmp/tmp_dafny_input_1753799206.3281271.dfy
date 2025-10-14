
function isMax(m: int, numbers: seq<int>): bool
{
    m in numbers &&
    forall i :: 0 <= i < |numbers| ==> numbers[i] <= m

}

method max(numbers: seq<int>) returns (result: int)
requires numbers != []
ensures isMax(result, numbers)
{
    result := numbers[0];
    // Invariant: result is the max of numbers[0..i)
    //            0 <= i <= |numbers|
    //            result in numbers[0..i)
    //            forall j :: 0 <= j < i ==> numbers[j] <= result
    var i: int := 1;
    while i < |numbers|
        invariant 1 <= i <= |numbers|
        invariant result in numbers[0..i]
        invariant forall j :: 0 <= j < i ==> numbers[j] <= result
    {
        if numbers[i] > result {
            result := numbers[i];
        }
        i := i + 1;
    }
    // At this point, i == |numbers|, so result is max of numbers[0..|numbers|] == numbers
    assert result in numbers;
    assert forall j :: 0 <= j < |numbers| ==> numbers[j] <= result;
}

method rolling_max(numbers: seq<int>) returns (result: seq<int>)
requires numbers != []
ensures |result| == |numbers|
ensures forall i :: 0 < i < |result| ==> isMax(result[i], numbers[0..(i+1)])
{
    var m := numbers[0];
    result := [m];
    var i: int := 1;
    while i < |numbers|
        invariant 1 <= i <= |numbers|
        invariant |result| == i
        invariant result[0] == numbers[0]
        invariant forall j :: 0 < j < i ==> isMax(result[j], numbers[0..(j+1)])
        invariant m in numbers[0..i]
        invariant forall j :: 0 <= j < i ==> numbers[j] <= m
    {
        if numbers[i] > m {
            m := numbers[i];
        }
        result := result + [m];
        i := i + 1;
    }
    // At this point, i == |numbers|, so |result| == |numbers|
    assert |result| == |numbers|;
    assert forall j :: 0 < j < |result| ==> isMax(result[j], numbers[0..(j+1)]);
}

function abs(a: real) : real {if a>0.0 then a else -a}
