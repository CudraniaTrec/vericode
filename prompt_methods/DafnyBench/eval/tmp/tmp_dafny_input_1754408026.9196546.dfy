
function min(a: int, b: int): int
    ensures min(a, b) <= a && min(a, b) <= b
    ensures min(a, b) == a || min(a, b) == b
{
    if a < b then a else b
}

method minMethod(a: int, b: int) returns (c: int)
    ensures c <= a && c <= b
    ensures c == a || c == b
    // Ou encore:
    ensures c == min(a, b)
{
    if a < b {
        c := a;
    } else {
        c := b;
    }
}

ghost function minFunction(a: int, b: int): int
    ensures minFunction(a, b) <= a && minFunction(a, b) <= b
    ensures minFunction(a, b) == a || minFunction(a, b) == b
{
    if a < b then a else b
}


// Return a minimum of a.
method minArray(a: array<int>) returns (m: int)
    requires a!= null  && a.Length > 0 ;

    ensures forall k | 0 <= k < a.Length :: m <= a[k]
    ensures exists k | 0 <= k < a.Length :: m == a[k]
{
    m := a[0]; // Initialise m avec le premier élément du tableau
    var i := 1;
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant m == (if forall j :: 0 <= j < i ==> a[j] >= m then m else old(m))
        invariant forall j | 0 <= j < i :: m <= a[j]
        invariant exists j | 0 <= j < i :: m == a[j]
    {
        if a[i] < m {
            m := a[i];
        }
        i := i + 1;
    }
    assert forall k | 0 <= k < a.Length :: m <= a[k];
    assert exists k | 0 <= k < a.Length :: m == a[k];
}

method Main(){
    var integer:= min(1,2);
    print(integer);
}

function abs(a: real) : real {if a>0.0 then a else -a}
