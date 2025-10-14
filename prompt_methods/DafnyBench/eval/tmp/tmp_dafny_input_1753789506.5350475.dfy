
ghost function Count(hi: nat, s:seq<int>): int
    requires 0 <= hi <= |s|
{
    if hi == 0 then 0
    else if s[hi-1]%2 == 0 then 1 + Count(hi-1, s) else Count(hi-1, s)
}

method FooCount(CountIndex:nat, a:seq<int>,b:array<int>) returns (p:nat)
    requires  CountIndex == 0 || (|a| == b.Length && 1 <= CountIndex <= |a|)
    modifies b
    ensures p == Count(CountIndex,a)
{
    if CountIndex == 0{
        p :=0;
    } else{
        assert |a| == b.Length && 0 <= CountIndex-1 < |a|;
        assert Count(CountIndex-1,a) <= Count(CountIndex,a);
        assert CountIndex > 0;
        if a[CountIndex-1]%2==0{
            var d := FooCount(CountIndex -1,a,b);
            assert d == Count(CountIndex-1,a);
            p:= d+1;
            assert p == 1 + Count(CountIndex-1,a);
            assert p == Count(CountIndex,a);
        }else{
            var d:= FooCount(CountIndex -1,a,b);
            assert d == Count(CountIndex-1,a);
            p:= d;
            assert p == Count(CountIndex-1,a);
            assert p == Count(CountIndex,a);
        }
        b[CountIndex-1] := p;
        assert b[CountIndex-1] == Count(CountIndex,a);
    }
}

method FooPreCompute(a:array<int>,b:array<int>)
    requires a.Length == b.Length
    modifies b
{
    var CountIndex := 1;
    while CountIndex != a.Length + 1
        invariant 1 <= CountIndex <= a.Length + 1
        invariant a.Length == b.Length
        invariant forall k :: 1 <= k < CountIndex ==> b[k-1] == Count(k, a[..])
    {   
        var p := FooCount(CountIndex,a[..],b);
        assert p == Count(CountIndex, a[..]);
        CountIndex := CountIndex +1;
    }
}

method ComputeCount(CountIndex:nat, a:seq<int>,b:array<int>) returns (p:nat)
    requires  CountIndex == 0 || (|a| == b.Length && 1 <= CountIndex <= |a|)
    modifies b
    ensures p == Count(CountIndex,a)
{
    if CountIndex == 0{
        p :=0;
    } else{
        assert |a| == b.Length && 0 <= CountIndex-1 < |a|;
        assert Count(CountIndex-1,a) <= Count(CountIndex,a);
        assert CountIndex > 0;
        if a[CountIndex-1]%2==0{
            var d := ComputeCount(CountIndex -1,a,b);
            assert d == Count(CountIndex-1,a);
            p:= d+1;
            assert p == 1 + Count(CountIndex-1,a);
            assert p == Count(CountIndex,a);
        }else{
            var d:= ComputeCount(CountIndex -1,a,b);
            assert d == Count(CountIndex-1,a);
            p:= d;
            assert p == Count(CountIndex-1,a);
            assert p == Count(CountIndex,a);
        }
        b[CountIndex-1] := p;  
        assert b[CountIndex-1] == Count(CountIndex,a);
    }
}

method PreCompute(a:array<int>,b:array<int>)returns(p:nat)
    requires a.Length == b.Length 
    modifies b
    ensures (b.Length == 0 || (a.Length == b.Length && 1 <= b.Length <= a.Length)) &&
    forall p::p == Count(b.Length,a[..]) ==> p==Count(b.Length,a[..])
{
    assert a.Length == b.Length;
    assert (b.Length == 0 || (a.Length == b.Length && 1 <= b.Length <= a.Length));
    assert forall p0 :: p0 == Count(b.Length,a[..]) ==> p0 == Count(b.Length,a[..]);
    p := ComputeCount(b.Length,a[..],b);
    assert p == Count(b.Length,a[..]);
}

method Evens(a:array<int>) returns (c:array2<int>)
    // modifies c
    // ensures  invariant forall i,j:: 0 <=i <m && 0 <= j < a.Length ==> j<i ==> c[i,j] == 0
{ 
     c := new int[a.Length,a.Length];
     var b := new int[a.Length];
     var foo := PreCompute(a,b); 
     var m := 0;
     while m != a.Length
        modifies c
        invariant 0 <= m <= a.Length
        invariant forall i,j :: 0 <= i < m && 0 <= j < a.Length && j < i ==> c[i,j] == 0
        invariant forall i,j :: 0 <= i < m && 0 <= j < a.Length && j >= i ==> 
            (i > 0 ==> c[i,j] == b[j] - b[i-1]) &&
            (i == 0 ==> c[i,j] == b[j])
     {  
        var n := 0;
        while n != a.Length
            modifies c
            invariant 0 <= n <= a.Length
            invariant forall k :: 0 <= k < n && k < m ==> c[m,k] == 0
            invariant forall k :: n <= k < a.Length && k < m ==> c[m,k] == 0
            invariant forall k :: n <= k < a.Length && k >= m ==> 
                (m > 0 ==> c[m,k] == b[k] - b[m-1]) &&
                (m == 0 ==> c[m,k] == b[k])
        {   
            if (n < m) {
                c[m,n] := 0;
                assert c[m,n] == 0;
            }else { 
                if m > 0 {
                    c[m,n] := b[n] - b[m-1];
                    assert c[m,n] == b[n] - b[m-1];
                }else{
                    c[m,n] := b[n];
                    assert c[m,n] == b[n];
                }
            }
            n := n + 1;
        }
        m := m + 1;
     }
}

method Mult(x:int, y:int) returns (r:int)
    requires x>= 0 && y>=0
    ensures r == x*y
{
    if x==0 {
        r:=0;
        assert r == 0*y;
        assert r == x*y;
    }else{
        var z:= Mult(x-1,y);
        assert z == (x-1)*y;
        r:=z+y;
        assert r == (x-1)*y + y;
        assert r == x*y;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
