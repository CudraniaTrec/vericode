method IsMonthWith30Days(month: int) returns (result: bool)
    requires 1 <= month <= 12
    ensures result <==> month == 4 || month == 6 || month == 9 || month == 11
{
    // The only months with 30 days are April, June, September, and November
    assert 1 <= month <= 12;
    result := month == 4 || month == 6 || month == 9 || month == 11;
    assert result <==> (month == 4 || month == 6 || month == 9 || month == 11);
}
function abs(a: real) : real {if a>0.0 then a else -a}
