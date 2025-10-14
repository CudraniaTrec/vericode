
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

    // Invariant: For all i0, j0 < |numbers|, if i0 < i, then for all j0, abs(numbers[i0] - numbers[j0]) >= threshold or i0 == j0
    // That is, no close elements have been found among indices < i
    // Also, if result is false, then no close elements have been found so far
    var i0: int; // dummy variable for quantifier use

    // Loop over i
    // Invariant: 0 <= i <= |numbers|
    // Invariant: forall i0, j0 :: 0 <= i0 < i && 0 <= j0 < |numbers| && i0 != j0 ==> abs(numbers[i0] - numbers[j0]) >= threshold
    // Invariant: result == false
    i := 0;
    while i < |numbers|
        invariant 0 <= i <= |numbers|
        invariant forall i0, j0 :: 0 <= i0 < i && 0 <= j0 < |numbers| && i0 != j0 ==> abs(numbers[i0] - numbers[j0]) >= threshold
        invariant result == false
    {
        // Loop over j
        // Invariant: 0 <= j <= |numbers|
        // Invariant: forall j0 :: 0 <= j0 < j && i != j0 ==> abs(numbers[i] - numbers[j0]) >= threshold
        j := 0;
        while j < |numbers|
            invariant 0 <= j <= |numbers|
            invariant forall j0 :: 0 <= j0 < j && i != j0 ==> abs(numbers[i] - numbers[j0]) >= threshold
            invariant result == false
        {
            if i != j && abs(numbers[i] - numbers[j]) < threshold {
                result := true;
                assert exists i', j' :: 0 <= i' < |numbers| && 0 <= j' < |numbers| && i' != j' && abs(numbers[i'] - numbers[j']) < threshold;
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    // At this point, result is still false, so no such pair exists
    assert forall i, j :: 0 <= i < |numbers| && 0 <= j < |numbers| && i != j ==> abs(numbers[i] - numbers[j]) >= threshold;
}

function abs(a: real) : real {if a>0.0 then a else -a}
