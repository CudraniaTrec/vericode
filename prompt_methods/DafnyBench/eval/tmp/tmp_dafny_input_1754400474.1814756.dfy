//Exercicio 1.a)
function sum (a:array<int>, i:int, j:int) :int
reads a
requires 0 <= i <= j <= a.Length
{
    if i == j then
        0
    else
        a[j-1] + sum(a, i, j-1)
}

//Exercicio 1.b)
method query (a:array<int>, i:int, j:int) returns (s:int)
requires 0 <= i <= j <= a.Length
ensures s == sum(a, i, j)
{
    s := 0;
    var aux := i;

    while (aux < j)
        invariant i <= aux <= j
        invariant s == sum(a, i, aux)
        decreases j - aux
    {
        s := s + a[aux];
        aux := aux + 1;
    }
    return s;
}

//Exercicio 1.c)
lemma queryLemma(a:array<int>, i:int, j:int, k:int)
    requires 0 <= i <= k <= j <= a.Length
    ensures  sum(a,i,k) + sum(a,k,j) == sum(a,i,j)
    decreases j - k
{
    if k == j {
        // sum(a, k, j) == 0, so sum(a, i, k) + 0 == sum(a, i, j)
        assert sum(a, i, k) + sum(a, k, j) == sum(a, i, j);
    } else {
        queryLemma(a, i, j-1, k);
        assert sum(a, i, k) + sum(a, k, j-1) == sum(a, i, j-1);
        assert sum(a, k, j) == a[j-1] + sum(a, k, j-1);
        assert sum(a, i, k) + sum(a, k, j) == sum(a, i, k) + a[j-1] + sum(a, k, j-1);
        assert sum(a, i, j) == a[j-1] + sum(a, i, j-1);
        assert sum(a, i, k) + sum(a, k, j) == sum(a, i, j);
    }
}

method queryFast (a:array<int>, c:array<int>, i:int, j:int) returns (r:int)
requires is_prefix_sum_for(a,c) && 0 <= i <= j <= a.Length < c.Length
ensures r == sum(a, i,j)
{
    r := c[j] - c[i];
    queryLemma(a,0,j,i);
    return r;
}

predicate is_prefix_sum_for (a:array<int>, c:array<int>)
reads c, a
{
    a.Length + 1 == c.Length
    && c[0] == 0
    && forall j :: 1 <= j <= a.Length ==> c[j] == sum(a,0,j)
}

///Exercicio 2.
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

method from_array<T>(a: array<T>) returns (l: List<T>)
requires a.Length > 0
ensures forall j::0 <= j < a.Length ==> mem(a[j],l)
{
    var i:= a.Length-1;
    l:= Nil;

    while (i >= 0)
        invariant -1 <= i < a.Length
        invariant l == from_array_helper(a, i+1, a.Length)
        invariant forall j:: i+1 <= j < a.Length ==> mem(a[j], l)
        decreases i + 1
    {
        l := Cons(a[i], l);
        i := i - 1;
    }
    return l;
}

function from_array_helper<T>(a: array<T>, start: int, end_: int): List<T>
    requires 0 <= start <= end_ <= a.Length
    decreases end_ - start
{
    if start == end_ then Nil else Cons(a[start], from_array_helper(a, start+1, end_))
}

function mem<T(==)> (x: T, l:List<T>) : bool
{
    match l
    case Nil => false
    case Cons(y,r)=> if (x==y) then true else mem(x,r)
}

function abs(a: real) : real {if a>0.0 then a else -a}
