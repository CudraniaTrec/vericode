
//Algorithm 1: From left to right return the first
method mmaximum1(v:array<int>) returns (i:int) 
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
{
    var j:=1; i:=0;
    // Invariant: i is the index of the maximum among v[0..j)
    while(j<v.Length)
        invariant 1 <= j <= v.Length
        invariant 0 <= i < j
        invariant forall k:: 0 <= k < j ==> v[i] >= v[k]
    {
        if(v[j] > v[i]){i:=j;}
        j:=j+1;
    }
    // At loop exit: j == v.Length, so i is index of maximum in v[0..v.Length)
    assert 0 <= i < v.Length;
    assert forall k:: 0 <= k < v.Length ==> v[i] >= v[k];
}

//Algorithm 2: From right to left return the last
method mmaximum2(v:array<int>) returns (i:int) 
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
{
    var j:=v.Length-2; i:=v.Length - 1;
    // Invariant: i is the index of the maximum among v[j+1..v.Length)
    while(j>=0)
        invariant -1 <= j < v.Length-1
        invariant 0 <= i < v.Length
        invariant forall k:: j+1 <= k < v.Length ==> v[i] >= v[k]
    {
        if(v[j] > v[i]){i:=j;}
        j:=j-1;
    }
    // At loop exit: j == -1, so i is index of maximum in v[0..v.Length)
    assert 0 <= i < v.Length;
    assert forall k:: 0 <= k < v.Length ==> v[i] >= v[k];
}


method mfirstMaximum(v:array<int>) returns (i:int)
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
ensures forall l:: 0<=l<i ==> v[i]>v[l]
//Algorithm: from left to right
{
    var j:=1; i:=0;
    // Invariant: i is the index of the first maximum among v[0..j)
    while(j<v.Length)
        invariant 1 <= j <= v.Length
        invariant 0 <= i < j
        invariant forall k:: 0 <= k < j ==> v[i] >= v[k]
        invariant forall l:: 0 <= l < i ==> v[i] > v[l]
    {
        if(v[j] > v[i]){i:=j;}
        j:=j+1;
    }
    // At loop exit: j == v.Length, so i is index of the first maximum in v[0..v.Length)
    assert 0 <= i < v.Length;
    assert forall k:: 0 <= k < v.Length ==> v[i] >= v[k];
    assert forall l:: 0 <= l < i ==> v[i] > v[l];
}

method mlastMaximum(v:array<int>) returns (i:int)
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
ensures forall l:: i<l<v.Length ==> v[i]>v[l]
{
    var j:=v.Length-2;
    i := v.Length-1;
    // Invariant: i is the index of the last maximum among v[j+1..v.Length)
    while(j>=0)
        invariant -1 <= j < v.Length-1
        invariant 0 <= i < v.Length
        invariant forall k:: j+1 <= k < v.Length ==> v[i] >= v[k]
        invariant forall l:: i < l < v.Length ==> v[i] > v[l]
    {
        if(v[j] > v[i]){i:=j;}
        j:=j-1;
    }
    // At loop exit: j == -1, so i is index of the last maximum in v[0..v.Length)
    assert 0 <= i < v.Length;
    assert forall k:: 0 <= k < v.Length ==> v[i] >= v[k];
    assert forall l:: i < l < v.Length ==> v[i] > v[l];
}

//Algorithm : from left to right
//Algorithm : from right to left

method mmaxvalue1(v:array<int>) returns (m:int)
requires v.Length>0
ensures m in v[..]
ensures forall k::0<=k<v.Length ==> m>=v[k]
{
    var i:=mmaximum1(v);
    m:=v[i];
    assert m in v[..];
    assert forall k:: 0 <= k < v.Length ==> m >= v[k];
}

method mmaxvalue2(v:array<int>) returns (m:int)
requires v.Length>0
ensures m in v[..]
ensures forall k::0<=k<v.Length ==> m>=v[k]
{
    var i:=mmaximum2(v);
    m:=v[i];
    assert m in v[..];
    assert forall k:: 0 <= k < v.Length ==> m >= v[k];
}

function abs(a: real) : real {if a>0.0 then a else -a}
