//Dafny Code

method posCount(list: array<int>) returns (res: int)
{
    res := 0;
    var i := 0;
    while i < list.Length
        invariant 0 <= i <= list.Length
        invariant res == (|{ j:int | 0 <= j < i && list[j] > 0 }|)
    {
        if list[i] > 0 {
            res := res + 1;
        }
        i := i + 1;
    }
}