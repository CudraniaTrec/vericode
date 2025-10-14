method CalculateLoss(costPrice: int, sellingPrice: int) returns (loss: int)
    requires costPrice >= 0 && sellingPrice >= 0
    ensures (costPrice > sellingPrice ==> loss == costPrice - sellingPrice) && (costPrice <= sellingPrice ==> loss == 0)
{
    if (costPrice > sellingPrice) {
        // costPrice > sellingPrice >= 0, so costPrice - sellingPrice >= 1
        assert costPrice - sellingPrice >= 1;
        loss := costPrice - sellingPrice;
        assert loss == costPrice - sellingPrice;
        assert loss >= 1;
    } else {
        // costPrice <= sellingPrice
        assert costPrice <= sellingPrice;
        loss := 0;
        assert loss == 0;
    }
    assert (costPrice > sellingPrice ==> loss == costPrice - sellingPrice) && (costPrice <= sellingPrice ==> loss == 0);
}
function abs(a: real) : real {if a>0.0 then a else -a}
