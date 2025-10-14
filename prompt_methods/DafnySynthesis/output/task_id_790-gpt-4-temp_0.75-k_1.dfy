method EveryEvenIndexHasEvenNumber(a: seq<int>) returns (res: bool)
{
    // Assume the sequence can be empty.
    res := true;
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant res ==> forall j :: 0 <= j < i && j % 2 == 0 ==> a[j] % 2 == 0
    {
        if i % 2 == 0 && a[i] % 2 != 0 {
            res := false;
            return;
        }
        i := i + 1;
    }
}