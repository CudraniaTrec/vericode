method DogYears(humanYears: int) returns (dogYears: int)
    requires humanYears >= 0
    ensures dogYears == 7 * humanYears
{
    // humanYears is non-negative by precondition
    assert humanYears >= 0;
    // Multiplication is safe (no overflow in Dafny's mathematical integers)
    dogYears := 7 * humanYears;
    // Postcondition holds by assignment
    assert dogYears == 7 * humanYears;
}
function abs(a: real) : real {if a>0.0 then a else -a}
