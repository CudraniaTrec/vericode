method IsBreakEven(costPrice: int, sellingPrice: int) returns (result: bool)
    requires costPrice >= 0 && sellingPrice >= 0
    ensures result <==> costPrice == sellingPrice
{
    result := costPrice == sellingPrice;
    assert result <==> costPrice == sellingPrice;
}
function abs(a: real) : real {if a>0.0 then a else -a}
