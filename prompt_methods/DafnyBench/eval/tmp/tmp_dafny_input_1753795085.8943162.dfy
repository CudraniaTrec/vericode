
method join(a:array<int>,b:array<int>) returns (c:array<int>)
ensures a[..] + b[..] == c[..]
ensures multiset(a[..] + b[..]) == multiset(c[..])
ensures multiset(a[..]) + multiset(b[..]) == multiset(c[..])
ensures a.Length+b.Length == c.Length

// Forall

ensures forall i :: 0<=i<a.Length ==> c[i] == a[i]
ensures forall i_2,j_2::
    a.Length <= i_2 < c.Length &&
    0<=j_2< b.Length && i_2 - j_2 == a.Length  ==> c[i_2] == b[j_2]

{

    c := new int[a.Length+b.Length];
    var i:= 0;
    while(i < a.Length)
        invariant 0 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> c[k] == a[k]
        invariant multiset(c[..i]) == multiset(a[..i])
        invariant c.Length == a.Length + b.Length
    {
        c[i] := a[i];
        i := i +1;
    }

    i:= a.Length;
    var j := 0;


    while(i < c.Length && j<b.Length) // missed j condition
        invariant a.Length <= i <= c.Length
        invariant 0 <= j <= b.Length
        invariant i - a.Length == j
        invariant forall k :: 0 <= k < a.Length ==> c[k] == a[k]
        invariant forall i_2, j_2 ::
            a.Length <= i_2 < i &&
            0 <= j_2 < j && i_2 - j_2 == a.Length ==> c[i_2] == b[j_2]
        invariant multiset(c[..a.Length]) == multiset(a[..])
        invariant multiset(c[a.Length..i]) == multiset(b[..j])
        invariant multiset(c[..i]) == multiset(a[..]) + multiset(b[..j])
        invariant c.Length == a.Length + b.Length
    //Sequences


    //Multiset

    
    // Forall 
    a.Length <= i_2 < i &&
    0<=j_2< j && i_2 - j_2 == a.Length  ==> c[i_2] == b[j_2] // curr loop
    0<=k_2<a.Length &&
    a.Length <= i_2 < i &&
    0<=j_2< j && i_2 - j_2 == a.Length  ==> c[i_2] == b[j_2] && c[k_2] == a[k_2] // prev loop+curr loop
    {
        
        c[i] := b[j];
        i := i +1;
        j := j +1;
    }

    assert j == b.Length;
    assert i == c.Length;
    assert b[..]==b[..b.Length];
    assert j + a.Length == c.Length;
    assert multiset(c[..a.Length]) == multiset(a[..a.Length]);
    assert multiset(b[..]) == multiset(b[..j]);
    assert multiset(c[a.Length..j+a.Length]) == multiset(c[a.Length..c.Length]);
    assert multiset(c[a.Length..c.Length]) == multiset(c[a.Length..c.Length]);
    assert multiset(c[a.Length..c.Length]) == multiset(b[..]);
    assert multiset(c[0..c.Length]) == multiset(c[0..a.Length]) + multiset(c[a.Length..c.Length]);
    
    // uncomment 


    
}


method Check(){
    var a := new int[][1,2,3];
    var b := new int[][4,5];
    var c := new int[][1,2,3,4,5];
    var d:= join(a,b);
    // print n[..];

}

function abs(a: real) : real {if a>0.0 then a else -a}
