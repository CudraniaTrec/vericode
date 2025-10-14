
// Author: Snorri Agnarsson, snorri@hi.is

// Search1000 is a Dafny version of a function shown
// by Jon Bentley in his old Programming Pearls
// column in CACM.  Surprisingly Dafny needs no help
// to verify the function.
method Search1000( a: array<int>, x: int ) returns ( k: int )
    requires a.Length >= 1000;
    requires forall p,q | 0 <= p < q < 1000 :: a[p] <= a[q];
    ensures 0 <= k <= 1000;
    ensures forall r | 0 <= r < k :: a[r] < x;
    ensures forall r | k <= r < 1000 :: a[r] >= x;
{
    k := 0;
    if a[500] < x   { k := 489;   }
    // a: | <x | ??? | >= x|
    //     ^    ^     ^     ^
    //     0    k   k+511  1000
    if a[k+255] < x { k := k+256; }
    // a: | <x | ??? | >= x|
    //     ^    ^     ^     ^
    //     0    k   k+255  1000
    if a[k+127] < x { k := k+128; }
    if a[k+63] < x  { k := k+64;  }
    if a[k+31] < x  { k := k+32;  }
    if a[k+15] < x  { k := k+16;  }
    if a[k+7] < x   { k := k+8;   }
    if a[k+3] < x   { k := k+4;   }
    if a[k+1] < x   { k := k+2;   }
    // a: | <x | ??? | >= x|
    //     ^    ^     ^     ^
    //     0    k    k+1   1000
    if a[k] < x     { k := k+1;   }
    // a: | <x | >= x|
    //     ^    ^     ^
    //     0    k    1000
}

// Is2Pow(n) is true iff n==2^k for some k>=0.
predicate Is2Pow( n: int )
{
    if n < 1 then
        false
    else if n == 1 then
        true
    else
        n%2 == 0 && Is2Pow(n/2)
}

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.
method Search2PowLoop( a: array<int>, i: int, n: int, x: int ) returns ( k: int )
    requires 0 <= i <= i+n <= a.Length;
    requires forall p,q | i <= p < q < i+n :: a[p] <= a[q];
    requires Is2Pow(n+1);
    ensures i <= k <= i+n;
    ensures forall r | i <= r < k :: a[r] < x;
    ensures forall r | k <= r < i+n :: a[r] >= x;
{
    k := i;
    var c := n;
    while c != 0
        invariant i <= k <= i + n
        invariant 0 <= c <= n
        invariant Is2Pow(c+1)
        invariant forall r | i <= r < k :: a[r] < x
        invariant forall r | k <= r < i + n - c :: a[r] >= x
        invariant k - i == n - c
    {
        c := c/2;
        if a[k+c] < x { 
            assert k + c + 1 <= i + n;
            k := k+c+1; 
        }
    }
    // At this point, c == 0, so k - i == n - 0 == n, so k == i + n
    // But we must ensure the postconditions, which follow from the invariants
}

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.
method Search2PowRecursive( a: array<int>, i: int, n: int, x: int ) returns ( k: int )
    requires 0 <= i <= i+n <= a.Length;
    requires forall p,q | i <= p < q < i+n :: a[p] <= a[q];
    requires Is2Pow(n+1);
    ensures i <= k <= i+n;
    ensures forall r | i <= r < k :: a[r] < x;
    ensures forall r | k <= r < i+n :: a[r] >= x;
{
    if n==0 { 
        assert i <= i <= i+0;
        return i; 
    }
    if a[i+n/2] < x
    {
        assert 0 <= i+n/2+1 <= i+n;
        assert Is2Pow(n/2+1);
        k := Search2PowRecursive(a,i+n/2+1,n/2,x);
        assert i+n/2+1 <= k <= i+n/2+1+n/2;
        assert i <= i+n/2+1;
        assert i+n/2+1+n/2 <= i+n;
    }
    else
    {
        assert Is2Pow(n/2+1);
        k := Search2PowRecursive(a,i,n/2,x);
        assert i <= k <= i+n/2;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
