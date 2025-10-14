
method barrier(v:array<int>,p:int) returns (b:bool)
//Give the precondition
//Give the postcondition
//{Implement and verify}
requires v.Length > 0
requires 0<=p<v.Length
ensures b==forall k,l::0<=k<=p && p<l<v.Length ==> v[k]<v[l]
{
    var i:=1;
    var max:=0;

    // Invariant: max is the index of the maximum element among v[0..i-1], and 1 <= i <= p+1
    // For all j in 0..i-1, v[j] <= v[max]
    // For all k,l with 0<=k<=p && p<l<i, v[k]<v[l] holds iff for all k in 0..p, v[k]<v[l]
    while(i<=p)
        invariant 1 <= i <= p+1
        invariant 0 <= max < i
        invariant forall j :: 0 <= j < i ==> v[j] <= v[max]
        invariant forall k,l :: 0 <= k <= p && p < l < i ==> v[k] < v[l]
    {
        if(v[i]>v[max]){
            max:=i;
        }
        i:=i+1;
    }

    // At this point, max is the index of the maximum element among v[0..p]
    // Now check that for all l in p+1..v.Length-1, v[max] < v[l]
    // If any v[i] <= v[max], then b should be false
    // Invariant: for all j in p+1..i-1, v[max] < v[j]
    while(i<v.Length && v[i]>v[max])
        invariant p+1 <= i <= v.Length
        invariant forall j :: p+1 <= j < i ==> v[max] < v[j]
        invariant forall k,l :: 0 <= k <= p && p < l < i ==> v[k] < v[l]
    {
        i:=i+1;
    }
    // At this point, i==v.Length iff for all l in p+1..v.Length-1, v[max] < v[l]
    // So, for all k in 0..p, v[k] <= v[max] < v[l] for all l in p+1..v.Length-1
    b:=i==v.Length;
    assert b == (forall k,l :: 0 <= k <= p && p < l < v.Length ==> v[k] < v[l]);
}

function abs(a: real) : real {if a>0.0 then a else -a}
