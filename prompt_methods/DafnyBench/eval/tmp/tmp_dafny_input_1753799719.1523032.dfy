
function R(n: nat): nat {
    if n == 0 then 0 else if R(n-1) > n then R(n-1) - n else R(n-1) + n
}

method calcR(n: nat) returns (r: nat)
    ensures r == R(n) 
{
    r := 0;
    var i := 0;
    while i < n 
        invariant 0 <= i <= n
        invariant r == R(i)
    {
       i := i + 1;
       if r  > i {
           r := r - i;
       } 
       else {
            r := r + i;
        }
       assert r == R(i);
    }
    assert r == R(n);
}

function abs(a: real) : real {if a>0.0 then a else -a}
