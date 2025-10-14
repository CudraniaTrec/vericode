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
  /* (| 1 = power(a,0) ^ 0<=n |)          - implied (a) */   // Can't assert this without a definition, so comment out
  s := 1;
  /* (| s = power(a,0) ^ 0<=n |)          - assignment */    // Can't assert this without a definition, so comment out
  var i := 0; 
  /* (| s = power(a,i) ^ i<=n |)          - assignment */    // Can't assert this without a definition, so comment out
  while (i < n)
    invariant 0 <= i <= n
    invariant s == power(a, i)
    decreases n - i
  {
    // Can't assert s == power(a,i) && i<=n && i<n without a definition, so comment out
    // Can't assert s*a == power(a,i+1) && i+1<=n without a definition, so comment out
    s := s*a;
    // Can't assert s == power(a,i+1) && i+1<=n without a definition, so comment out
    i := i+1;
    // Can't assert s == power(a,i) && i<=n without a definition, so comment out
  }
  // Can't assert s == power(a,i) && i<=n && !(i<n) without a definition, so comment out
  // Can't assert s == power(a,n) without a definition, so comment out
}

axiom (forall a:int, n:int :: 0 <= a && 0 <= n && n > 0 ==> power(a, n) == power(a, n-1) * a);
axiom (forall a:int :: 0 <= a ==> power(a, 0) == 1);

function abs(a: real) : real {if a>0.0 then a else -a}
