method HasNoProfitNoLoss(costPrice: int, sellingPrice: int) returns (noProfitNoLoss: bool)
    ensures noProfitNoLoss == (costPrice == sellingPrice)
{
    noProfitNoLoss := costPrice == sellingPrice;
}