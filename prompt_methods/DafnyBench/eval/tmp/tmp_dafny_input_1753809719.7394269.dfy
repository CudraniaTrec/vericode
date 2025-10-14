method ordenar_mergesort(V : array?<int>)

    requires V != null
    
    modifies V

{
    
    mergesort(V, 0, V.Length - 1) ;
    
}



method mergesort(V : array?<int>, c : int, f : int) 

    requires V != null
    requires c >= 0 && f <= V.Length

    modifies V
    decreases if f >= c then f - c else 0
{
    
    if c < f {
        
        var m : int ;
        m := c + (f - c) / 2 ;
        
        mergesort(V, c, m) ;
        mergesort(V, m + 1, f) ;

        mezclar(V, c, m, f) ;
        
    }
    
}



method mezclar(V: array?<int>, c : int, m : int, f : int)

    requires V != null
    requires c <= m <= f
    requires 0 <= c <= V.Length
    requires 0 <= m <= V.Length
    requires 0 <= f <= V.Length

    modifies V

{

    var V1 : array?<int> ;
    var j  : nat ;

    V1 := new int[m - c + 1] ;
    j  := 0 ;
    
    while j < V1.Length
        invariant 0 <= j <= V1.Length
        invariant forall t :: 0 <= t < j ==> V1[t] == V[c + t]
        invariant c + j <= V.Length
    {
        // c + j < V.Length is not always true, but c + j <= V.Length is.
        V1[j] := V[c + j] ;
        j := j + 1 ;
    }


    var V2 : array?<int> ;
    var k  : nat ;

    V2 := new int[f - m] ; 
    k  := 0 ;
    
    while k < V2.Length
        invariant 0 <= k <= V2.Length
        invariant forall t :: 0 <= t < k ==> V2[t] == V[m + 1 + t]
        invariant m + 1 + k <= V.Length
    {
        V2[k] := V[m + 1 + k] ;
        k := k + 1 ;
    }


    var i : nat ;

    i := 0 ;
    j := 0 ;
    k := 0 ;
    
    while j < V1.Length || k < V2.Length
        invariant 0 <= j <= V1.Length
        invariant 0 <= k <= V2.Length
        invariant 0 <= i <= V1.Length + V2.Length
        invariant forall t :: 0 <= t < j ==> V[c + t] == V1[t]
        invariant forall t :: 0 <= t < k ==> V[c + j + t] == V2[t]
        invariant i == j + k
        invariant c + i <= V.Length
        decreases V1.Length + V2.Length - i
    {
        if j < V1.Length && (k >= V2.Length || V1[j] <= V2[k]) {
            assert c + i < V.Length;
            assert j < V1.Length;
            V[c + i] := V1[j] ;
            j := j + 1 ;
        } else if k < V2.Length {
            assert c + i < V.Length;
            assert k < V2.Length;
            V[c + i] := V2[k] ;
            k := k + 1 ;
        }
        i := i + 1 ;
    }
    
}

function abs(a: real) : real {if a>0.0 then a else -a}
