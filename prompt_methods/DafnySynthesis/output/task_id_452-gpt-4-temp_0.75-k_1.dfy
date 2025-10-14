//Dafny Code

method LossAmount(costPrice: int, salePrice: int) returns (loss: int)
{
    if salePrice < costPrice {
        loss := costPrice - salePrice;
    } else {
        loss := 0;
    }
}