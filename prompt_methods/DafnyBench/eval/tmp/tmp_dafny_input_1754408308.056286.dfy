
function Power(n: nat): nat {
    if n == 0 then 1 else 2 * Power(n - 1)
}

method ComputePower(N: int) returns (y: nat) requires N >= 0
    ensures y == Power(N)
{
    y := 1;
    var x := 0; 
    while x != N
        invariant 0 <= x <= N
        invariant y == Power(x)
        decreases N - x
    {
        x, y := x + 1, y + y;
    } 
}

method Max(a: array<nat>) returns (m: int)
    ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
    ensures (m == 0 && a.Length == 0) || exists i :: 0 <= i < a.Length && m == a[i] 
{
    m := 0;
    var n := 0;
    while n != a.Length
        invariant 0 <= n <= a.Length
        invariant (n == 0 ==> m == 0)
        invariant (n > 0 ==> exists i :: 0 <= i < n && m == a[i])
        invariant forall i :: 0 <= i < n ==> a[i] <= m
        decreases a.Length - n
    {
        if m < a[n] {
            m := a[n]; 
        }
        n := n + 1; 
    }
}

method Cube(n: nat) returns (c: nat) 
    ensures c == n * n * n
{
    c := 0;
    var i := 0;
    while i != n
        invariant 0 <= i <= n
        invariant c == i * i * i
        decreases n - i
    {
        c := c + (i * i * 3 + i * 3 + 1);
        i := i + 1;
    }
}

method IncrementMatrix(a: array2<int>)
    modifies a
    ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
{
    var m := 0;
    while m != a.Length0
        invariant 0 <= m <= a.Length0
        invariant forall i, j :: 0 <= i < m && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
        invariant forall i, j :: m <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j])
        decreases a.Length0 - m
    {
        var n := 0;
        while n != a.Length1
            invariant 0 <= n <= a.Length1
            invariant forall j :: 0 <= j < n ==> a[m,j] == old(a[m,j]) + 1
            invariant forall j :: n <= j < a.Length1 ==> a[m,j] == old(a[m,j])
            decreases a.Length1 - n
        {
            a[m,n] := a[m,n] + 1;
            n := n + 1; 
        }
        m := m + 1; 
    }
}

method CopyMatrix(src: array2, dst: array2)
    requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
    modifies dst
    ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j]) 
{
    var m := 0;
    while m != src.Length0
        invariant 0 <= m <= src.Length0
        invariant forall i, j :: 0 <= i < m && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j])
        invariant forall i, j :: m <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(dst[i,j])
        decreases src.Length0 - m
    {
        var n := 0;
        while n != src.Length1
            invariant 0 <= n <= src.Length1
            invariant forall j :: 0 <= j < n ==> dst[m,j] == old(src[m,j])
            invariant forall j :: n <= j < src.Length1 ==> dst[m,j] == old(dst[m,j])
            decreases src.Length1 - n
        {
            dst[m,n] := src[m,n]; n := n + 1;
        }
        m := m + 1; 
    }
}

method DoubleArray(src: array<int>, dst: array<int>)
    requires src.Length == dst.Length
    modifies dst
    ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
{
    var n := 0;
    while n != src.Length
        invariant 0 <= n <= src.Length
        invariant forall i :: 0 <= i < n ==> dst[i] == 2 * old(src[i])
        invariant forall i :: n <= i < src.Length ==> dst[i] == old(dst[i])
        decreases src.Length - n
    {
        dst[n] := 2 * src[n]; n := n + 1;
    } 
}

method RotateLeft(a: array)
    requires a.Length > 0
    modifies a
    ensures forall i :: 0 <= i < a.Length - 1 ==> a[i] == old(a[(i+1)]) 
    ensures a[a.Length -1] == old(a[0])
{
    var n := 0;
    while n != a.Length - 1
        invariant 0 <= n <= a.Length - 1
        invariant forall i :: 0 <= i < n ==> a[i] == old(a[i+1])
        invariant forall i :: n <= i < a.Length - 1 ==> a[i] == old(a[i+1])
        invariant a[a.Length-1] == old(a[0])
        decreases a.Length - 1 - n
    {
        a[n], a[n+1] := a[n+1], a[n];
        n := n + 1; 
    }
}

method RotateRight(a: array)
    requires a.Length > 0
    modifies a
    ensures forall i :: 1<= i < a.Length ==> a[i] == old(a[(i-1)]) 
    ensures a[0] == old(a[a.Length-1])
{
    var n := 1;
    var tmp := a[0];
    while n != a.Length
        invariant 1 <= n <= a.Length
        invariant a[0] == old(a[a.Length-n])
        invariant forall i :: 1 <= i < n ==> a[i] == old(a[a.Length-n+i])
        invariant forall i :: n <= i < a.Length ==> a[i] == old(a[i-n])
        decreases a.Length - n
    {
        var t := a[n];
        a[n] := tmp;
        tmp := t;
        n := n + 1;
    }
    a[0] := tmp;
}

function abs(a: real) : real {if a>0.0 then a else -a}
