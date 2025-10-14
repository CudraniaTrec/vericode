predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}


method mpositive(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{
    var i:=0;
    //1. assert positive(v[..0])
    assert positive(v[..0]);
    while i<v.Length && v[i]>=0
        invariant 0 <= i <= v.Length
        invariant positive(v[..i])
    {
        //2. assert 0<=i<v.Length && positive(v[..i]);
        assert 0<=i<v.Length && positive(v[..i]);
        i:=i+1;
        //2. assert 0<=i<=v.Length && positive(v[..i]);
        assert 0<=i<=v.Length && positive(v[..i]);
    }
    //3. assert i==v.Length ==> positive(v[..]);
    assert i==v.Length ==> positive(v[..]);
    //3. assert i<v.Length => v[i]<0;
    assert i<v.Length ==> v[i]<0;
    b := i==v.Length;
}

method mpositive3(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{
    var i:=0; b:=true;
    while(i<v.Length && b)
        invariant 0 <= i <= v.Length
        invariant b ==> positive(v[..i])
        invariant !b ==> (exists j:: 0<=j<i && v[j]<0)
    {
        b:=v[i]>=0;
        i:=i+1;
    }
}

method mpositive4(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{
    var i:=0; b:=true;
    while(i<v.Length && b)
        invariant 0 <= i <= v.Length
        invariant b ==> positive(v[..i])
        invariant !b ==> (exists j:: 0<=j<i && v[j]<0)
    {
        b:=v[i]>=0;
        i:=i+1;
    }
    
}

method mpositivertl(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{
    var i:=v.Length-1;
    while(i>=0 && v[i]>=0)
        invariant -1 <= i < v.Length
        invariant positive(v[..i+1])
    {
        i:=i-1;
    }
    b:= i==-1;
}

function abs(a: real) : real {if a>0.0 then a else -a}
