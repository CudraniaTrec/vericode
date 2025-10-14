method MonthHas31Days(month: int) returns (result: bool)
    requires 1 <= month <= 12
    ensures result <==> month in {1, 3, 5, 7, 8, 10, 12}
{
    // The result is true iff the month is one with 31 days
    assert 1 <= month <= 12;
    assert (month in {1, 3, 5, 7, 8, 10, 12}) <==> (month == 1 || month == 3 || month == 5 || month == 7 || month == 8 || month == 10 || month == 12);
    result := month in {1, 3, 5, 7, 8, 10, 12};
    assert result <==> month in {1, 3, 5, 7, 8, 10, 12};
}
function abs(a: real) : real {if a>0.0 then a else -a}
