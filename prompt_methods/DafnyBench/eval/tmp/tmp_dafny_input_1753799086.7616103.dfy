function abs(x: real): real
{
  if x < 0.0 then -x else x
}

method has_close_elements(numbers: seq<real>, threshold: real) returns (result: bool)
    ensures result <==> exists i, j ::
      0 <= i < |numbers| &&
      0 <= j < |numbers| &&
      i != j &&
      abs(numbers[i] - numbers[j]) < threshold
    ensures result ==> |numbers| > 1
{
    result := false;

    var i: int := 0;
    while i < |numbers|
        invariant 0 <= i <= |numbers|
        invariant forall i0, j0 :: 0 <= i0 < i && 0 <= j0 < |numbers| && i0 != j0 ==> abs(numbers[i0] - numbers[j0]) >= threshold
        invariant result == false
    {
        var j: int := 0;
        while j < |numbers|
            invariant 0 <= j <= |numbers|
            invariant forall j0 :: 0 <= j0 < j && i != j0 ==> abs(numbers[i] - numbers[j0]) >= threshold
            invariant result == false
        {
            if i != j && abs(numbers[i] - numbers[j]) < threshold {
                result := true;
                assert 0 <= i < |numbers| && 0 <= j < |numbers| && i != j && abs(numbers[i] - numbers[j]) < threshold;
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    // At this point, result is false, so no such pair exists
    assert forall i1, j1 :: 0 <= i1 < |numbers| && 0 <= j1 < |numbers| && i1 != j1 ==> abs(numbers[i1] - numbers[j1]) >= threshold;
}
function abs(a: real) : real {if a>0.0 then a else -a}
