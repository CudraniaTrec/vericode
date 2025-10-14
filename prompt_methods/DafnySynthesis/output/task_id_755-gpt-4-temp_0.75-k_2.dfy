method SecondSmallest(a: array<int>) returns (secondMin: int)
    requires a != null && a.Length >= 2
    ensures exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && i != j && 
                        ((a[i] <= a[j] && a[i] <= secondMin && a[j] == secondMin) || 
                         (a[j] <= a[i] && a[j] <= secondMin && a[i] == secondMin))
    ensures forall i :: 0 <= i < a.Length ==> a[i] >= secondMin || exists j :: 0 <= j < a.Length && a[j] < secondMin
{
    var min, sec : int;
    if a[0] < a[1] {
        min := a[0];
        sec := a[1];
    } else {
        min := a[1];
        sec := a[0];
    }

    var i := 2;
    while i < a.Length
        invariant 2 <= i <= a.Length
        invariant (forall j :: 0 <= j < i ==> a[j] >= min)
        invariant (forall j :: 0 <= j < i ==> a[j] >= sec || a[j] == min)
        invariant min <= sec
    {
        if a[i] < min {
            sec := min;
            min := a[i];
        } else if a[i] < sec && a[i] != min {
            sec := a[i];
        }
        i := i + 1;
    }

    secondMin := sec;
}