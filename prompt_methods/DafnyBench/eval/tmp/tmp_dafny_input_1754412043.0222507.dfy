
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

    // Strongest possible invariant before the outer loop:
    // For all i0, j0 in range, if i0 != j0 and both indices are < i,
    // then abs(numbers[i0] - numbers[j0]) >= threshold
    // (i.e., no close elements among indices < i)
    var i0: int;
    var j0: int;

    // Outer loop
    i := 0;
    while i < |numbers|
        invariant 0 <= i <= |numbers|
        invariant forall i0, j0 :: 
            0 <= i0 < |numbers| && 0 <= j0 < |numbers| && i0 != j0 && (i0 < i && j0 < i) ==>
                abs(numbers[i0] - numbers[j0]) >= threshold
        invariant !result
    {
        // Inner loop
        var j: int := 0;
        while j < |numbers|
            invariant 0 <= j <= |numbers|
            invariant forall j0 :: 
                0 <= j0 < j ==>
                    (i != j0 ==> abs(numbers[i] - numbers[j0]) >= threshold)
            invariant forall i0, j0 :: 
                0 <= i0 < |numbers| && 0 <= j0 < |numbers| && i0 != j0 && (i0 < i && j0 < i) ==>
                    abs(numbers[i0] - numbers[j0]) >= threshold
            invariant !result
        {
            if i != j && abs(numbers[i] - numbers[j]) < threshold {
                result := true;
                assert exists i', j' :: 
                    i' == i && j' == j &&
                    0 <= i' < |numbers| && 0 <= j' < |numbers| &&
                    i' != j' &&
                    abs(numbers[i'] - numbers[j']) < threshold;
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    // At this point, result is false, so there are no close elements
    assert forall i, j :: 
        0 <= i < |numbers| && 0 <= j < |numbers| && i != j ==>
            abs(numbers[i] - numbers[j]) >= threshold;
}

function abs(a: real) : real {if a>0.0 then a else -a}
