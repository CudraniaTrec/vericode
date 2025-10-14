
//power -- Stephanie Renee McIntyre
//Based on the code used in the course overheads for Fall 2018

//There is no definition for power, so this function will be used for validating that our imperative program is correct.
function power(a: int, n: int): int //function for a to the power of n
  requires 0 <= a && 0 <= n;

//Our code from class
method compute_power(a: int, n: int) returns (s: int)
/*Pre-Condition*/   requires n >= 0 && a >= 0;
/*Post-Condition*/  ensures s == power(a,n);
{
  /* (| a >= 0 ^ n >= 0 |)                - Pre-Condition: requires statement above */
  /* (| 1 = power(a,0) ^ 0<=n |)          - implied (a) */   assert 1 == power(a,0) && 0<=n;
  s := 1;
  /* (| s = power(a,0) ^ 0<=n |)          - assignment */    assert s == power(a,0) && 0<=n;
  var i := 0; 
  /* (| s = power(a,i) ^ i<=n |)          - assignment */    assert s == power(a,i) && i<=n;
  while (i < n)
    invariant 0 <= i <= n
    invariant s == power(a, i)
    decreases n - i
  {
    /* (| s = power(a,i) ^ i<=n ^ i<n |)  - partial-while */ assert s == power(a,i) && i<=n && i<n;
    /* (| s*a = power(a,i+1) ^ i+1<=n |)  - implied (b) */   assert s*a == power(a,i+1) && i+1<=n;
    s := s*a;
    /* (| s = power(a,i+1) ^ i+1<=n |)    - assignment */    assert s == power(a,i+1) && i+1<=n;
    i := i+1;
    /* (| s = power(a,i) ^ i<=n |)        - assignment */    assert s == power(a,i) && i<=n;
  }
  /* (| s = power(a,i) ^ i<=n ^ -(i<n) |) - partial-while */ assert s == power(a,i) && i<=n && !(i<n);
  /* (| s = power(a,n) |)                 - implied (c) //Post-Condition: ensures statement above */
}

function abs(a: real) : real {if a>0.0 then a else -a}
