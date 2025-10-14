
/*                                      Cumulative Sums over Arrays                                        */

/*
    Daniel Cavalheiro   57869
    Pedro Nunes         57854
*/



//(a)

function sum(a: array<int>, i: int, j: int): int
    reads a
    requires 0 <= i <= j <= a.Length
    decreases j - i
{
    if (i == j) then 0
    else a[i] + sum(a, i+1, j)
}



//(b)

method query(a: array<int>, i: int, j: int) returns (res:int)
    requires 0 <= i <= j <= a.Length
    ensures res == sum(a, i, j)
{
    res := 0;
    var k := i;

    while(k < j)
        invariant i <= k <= j
        invariant res == sum(a, i, k)
        invariant 0 <= i <= j <= a.Length
        decreases j - k
    {
        res := res + a[k];
        k := k + 1;
    }
    // At this point, k == j and res == sum(a, i, j)
}



//(c)

predicate is_prefix_sum_for (a: array<int>, c: array<int>)
    requires a.Length + 1 == c.Length
    requires c[0] == 0
    reads c, a
{
    forall i: int :: 0 <= i < a.Length ==> c[i+1] == c[i] + a[i]
}

lemma aux(a: array<int>, c: array<int>, i: int, j: int)
    requires 0 <= i <= j <= a.Length
    requires a.Length + 1 == c.Length
    requires c[0] == 0
    requires is_prefix_sum_for(a, c)
    ensures forall k: int :: i <= k <= j ==> sum(a, i, k) + sum(a, k, j) == c[k] - c[i] + c[j] - c[k] //sum(a, i, j) == c[j] - c[i]
{
    // Prove sum(a, i, k) == c[k] - c[i] for all i <= k <= j
    var start := i;
    while start <= j
        invariant i <= start <= j+1
        invariant forall k: int :: i <= k < start ==> sum(a, i, k) == c[k] - c[i]
        decreases j + 1 - start
    {
        if start > i {
            // sum(a, i, start) == sum(a, i, start-1) + a[start-1]
            // c[start] - c[i] == (c[start-1] + a[start-1]) - c[i] == (c[start-1] - c[i]) + a[start-1]
            // By induction hypothesis: sum(a, i, start-1) == c[start-1] - c[i]
            assert sum(a, i, start) == sum(a, i, start-1) + a[start-1];
            assert sum(a, i, start-1) == c[start-1] - c[i];
            assert c[start] == c[start-1] + a[start-1];
            assert sum(a, i, start) == c[start] - c[i];
        }
        start := start + 1;
    }
    // Now, for all k: i <= k <= j, sum(a, i, k) == c[k] - c[i]
    // So for any k in i..j, sum(a, i, k) + sum(a, k, j) == (c[k] - c[i]) + (c[j] - c[k]) == c[j] - c[i]
    // This proves the ensures clause.
}

method queryFast(a: array<int>, c: array<int>, i: int, j: int) returns (r: int)
    requires a.Length + 1 == c.Length && c[0] == 0
    requires 0 <= i <= j <= a.Length
    requires is_prefix_sum_for(a,c)  
    ensures r == sum(a, i, j)
{   
    // By aux, sum(a, i, j) == c[j] - c[i]
    r := c[j] - c[i];    
}




method Main()
{
    var x := new int[10];
    x[0], x[1], x[2], x[3] := 2, 2, 1, 5;
    var y := sum(x, 0, x.Length);
    //assert y == 10;
    var c := new int[11];
    c[0], c[1], c[2], c[3], c[4] := 0, 2, 4, 5, 10;
   // var r := queryFast(x, c, 0, x.Length);
    
}

function abs(a: real) : real {if a>0.0 then a else -a}
