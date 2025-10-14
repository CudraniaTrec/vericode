method CountPositives(a: array<int>) returns (count: int)
    ensures 0 <= count <= a.Length
    ensures count == |set i :: 0 <= i < a.Length && a[i] > 0|
{
    count := 0;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant 0 <= count <= i
        invariant count == |set j :: 0 <= j < i && a[j] > 0|
    {
        if a[i] > 0 {
            count := count + 1;
        }
        i := i + 1;
    }
}