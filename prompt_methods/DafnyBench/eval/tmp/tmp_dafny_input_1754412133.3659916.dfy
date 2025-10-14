
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
    // Invariant: 1 <= i <= |numbers|
    for i := 1 to |numbers|
        invariant 1 <= i <= |numbers|
        invariant result in numbers[0..i]
        invariant forall j :: 0 <= j < i ==> numbers[j] <= result
    {
        if numbers[i] > result {
            result := numbers[i];
        }
        // assert result in numbers[0..i+1];
        // assert forall j :: 0 <= j < i+1 ==> numbers[j] <= result;
    }
    // assert isMax(result, numbers);
}

method rolling_max(numbers: seq<int>) returns (result: seq<int>)
requires numbers != []
ensures |result| == |numbers|
ensures forall i :: 0 < i < |result| ==> isMax(result[i], numbers[0..(i+1)])
{
    var m := numbers[0];
    result := [m];
    // Invariant: |result| == i
    // Invariant: 1 <= i <= |numbers|
    // Invariant: forall j :: 0 < j < i ==> isMax(result[j], numbers[0..(j+1)])
    // Invariant: m == max(numbers[0..i])
    for i := 1 to |numbers|
        invariant 1 <= i <= |numbers|
        invariant |result| == i
        invariant forall j :: 0 < j < i ==> isMax(result[j], numbers[0..(j+1)])
        invariant m in numbers[0..i]
        invariant forall j :: 0 <= j < i ==> numbers[j] <= m
    {
        if numbers[i] > m {
            m := numbers[i];
        }
        result := result + [m];
        // assert result[i] == m;
        // assert isMax(m, numbers[0..(i+1)]);
    }
    // assert |result| == |numbers|;
    // assert forall i :: 0 < i < |result| ==> isMax(result[i], numbers[0..(i+1)]);
}

function abs(a: real) : real {if a>0.0 then a else -a}
