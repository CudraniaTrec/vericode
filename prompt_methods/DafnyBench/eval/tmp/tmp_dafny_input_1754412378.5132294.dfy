
method find(a: array<int>, key: int) returns(index: int)
    requires a.Length > 0;
    ensures 0 <= index <= a.Length;
    ensures index < a.Length ==> a[index] == key;
{
    index := 0;
    while index < a.Length && a[index] != key 
        invariant 0 <= index <= a.Length;
        invariant forall j :: 0 <= j < index ==> a[j] != key;
    {
        index := index + 1;
    }
    assert 0 <= index <= a.Length;
    assert forall j :: 0 <= j < index ==> a[j] != key;
    assert index < a.Length ==> a[index] == key;
}

function abs(a: real) : real {if a>0.0 then a else -a}
