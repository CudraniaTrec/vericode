
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

    // Invariant: max holds the index of the maximum element in v[0..i-1]
    // Invariant: 1 <= i <= p+1
    // Invariant: forall k :: 0 <= k < i ==> v[k] <= v[max]
    // Invariant: max <= p
    while(i<=p)
        invariant 1 <= i <= p+1
        invariant 0 <= max < i
        invariant max <= p
        invariant forall k :: 0 <= k < i ==> v[k] <= v[max]
    {
        if(v[i]>v[max]){
            max:=i;
        }

        i:=i+1;
    }

    // At this point, max is the index of the maximum element in v[0..p]
    // Now check that for all j in (p+1)..(v.Length-1), v[max] < v[j]
    // Invariant: p+1 <= i <= v.Length
    // Invariant: forall l :: p < l < i ==> v[max] < v[l]
    while(i<v.Length && v[i]>v[max])
        invariant p+1 <= i <= v.Length
        invariant forall l :: p < l < i ==> v[max] < v[l]
    {
        i:=i+1;
    }
    // At this point, i == v.Length iff forall l :: p < l < v.Length ==> v[max] < v[l]

    // Now, for all k in 0..p and l in (p+1)..(v.Length-1), v[k] < v[l] iff v[max] < v[l]
    // because v[max] is the maximum of v[0..p]
    b:=i==v.Length;
}

function abs(a: real) : real {if a>0.0 then a else -a}
