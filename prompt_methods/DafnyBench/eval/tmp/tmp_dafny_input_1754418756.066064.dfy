
method Getmini(a:array<int>) returns(mini:nat) 
requires a.Length > 0
ensures 0 <= mini < a.Length // mini is an index of a
ensures forall x :: 0 <= x < a.Length ==> a[mini] <= a[x] // a[mini] is the minimum value
ensures forall x :: 0 <= x < mini ==> a[mini] < a[x] // a[mini] is the first min
{
    // find mini
    var min:int := a[0];
    var i:int := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> min <= a[j]
        invariant exists j :: 0 <= j < i ==> min == a[j] || i == 0
        decreases a.Length - i
    {
        if a[i] < min {
            min := a[i];
        }
        i := i + 1;
    }

    assert exists j :: 0 <= j < a.Length && a[j] == min;
    assert forall j :: 0 <= j < a.Length ==> min <= a[j];

    // find first occurance
    var k:int := 0;
    while k < a.Length 
        invariant 0 <= k <= a.Length
        invariant forall j :: 0 <= j < k ==> a[j] != min
        decreases a.Length - k
    {
        if a[k] == min {
            return k;
        }
        k := k + 1;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
