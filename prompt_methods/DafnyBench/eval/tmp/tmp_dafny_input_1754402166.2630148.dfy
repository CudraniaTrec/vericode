
method mroot1(n:int) returns (r:int) //Cost O(root n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{
    r:=0;
    while (r+1)*(r+1) <=n
     invariant r >= 0
     invariant r*r <= n
     invariant (r+1)*(r+1) > n ==> r*r <= n < (r+1)*(r+1)
     invariant (r+1)*(r+1) <= n ==> (r+1)*(r+1) <= n
     decreases n - r
     {
       assert r+1 >= 1;
       r:=r+1;
     }
    assert r >= 0;
    assert r*r <= n;
    assert (r+1)*(r+1) > n;
}

method mroot2(n:int) returns (r:int) //Cost O(n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{
    r:=n;
    while n<r*r
      invariant 0 <= r <= n
      invariant r*r > n
      decreases r
    {
        assert r > 0;
        r:=r-1;
    }
    assert r >= 0;
    assert r*r <= n;
    assert (r+1)*(r+1) > n;
}

method mroot3(n:int) returns (r:int) //Cost O(log n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{   var y:int;
    var h:int;
    r:=0;
    y:=n+1;
    //Search in interval [0,n+1) 
    while (y!=r+1) //[r,y]
      invariant 0 <= r < y <= n+1
      invariant r*r <= n
      invariant y*y > n
      invariant forall k :: r < k < y ==> k*k > n || k*k <= n
      decreases y - r
     {
       h:=(r+y)/2;
       assert r < h < y;
       if (h*h<=n)
         {r:=h;}
       else
         {y:=h;} 
     }
    assert r >= 0;
    assert r*r <= n;
    assert (r+1)*(r+1) > n;
}

function abs(a: real) : real {if a>0.0 then a else -a}
