method mulEvenOdd(list1: array<nat>) returns (res:nat)
{
    var firstEven: nat := 0;
    var foundEven: bool := false;
    var firstOdd: nat := 0;
    var foundOdd: bool := false;

    var i := 0;
    while i < list1.Length && !(foundEven && foundOdd)
        decreases list1.Length - i
    {
        if !foundEven && list1[i] % 2 == 0 {
            firstEven := list1[i];
            foundEven := true;
        }
        if !foundOdd && list1[i] % 2 == 1 {
            firstOdd := list1[i];
            foundOdd := true;
        }
        i := i + 1;
    }
    if foundEven && foundOdd {
        res := firstEven * firstOdd;
    } else {
        // If not found, define what to return, here return 0.
        res := 0;
    }
}