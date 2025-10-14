//Dafny Code

method ContainsConsecutiveNumbers(a: array<int>) returns (res: bool)
    requires a != null
    ensures res <==> 
        (if a.Length == 0 then false 
         else 
            var s := set i | 0 <= i < a.Length :: a[i];
            s.Card == a.Length &&
            (forall x :: x in s ==> (a[0] <= x <= a[0] + a.Length - 1 || a[0] - a.Length + 1 <= x <= a[0]))
        )
{
    if a.Length == 0 {
        return false;
    }

    var min := a[0];
    var max := a[0];
    var found := map<int, bool>{};

    // Find min, max, and check for duplicates
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> found[a[j]]
        invariant i > 0 ==> min == (if forall k :: 0 <= k < i ==> a[k] >= min then min else min)
        invariant i > 0 ==> max == (if forall k :: 0 <= k < i ==> a[k] <= max then max else max)
    {
        if a[i] in found {
            return false; // duplicate found
        }
        found := found[a[i] := true];
        if a[i] < min {
            min := a[i];
        }
        if a[i] > max {
            max := a[i];
        }
        i := i + 1;
    }

    if max - min + 1 != a.Length {
        return false;
    }

    return true;
}