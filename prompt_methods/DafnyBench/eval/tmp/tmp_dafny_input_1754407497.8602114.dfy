
method SquareElements(a: array<int>) returns (squared: array<int>)
    ensures squared.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> squared[i] == a[i] * a[i]
{
    squared := new int[a.Length];
    var i: int := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant squared.Length == a.Length
        invariant forall j :: 0 <= j < i ==> squared[j] == a[j] * a[j]
    {
        squared[i] := a[i] * a[i];
        i := i + 1;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
