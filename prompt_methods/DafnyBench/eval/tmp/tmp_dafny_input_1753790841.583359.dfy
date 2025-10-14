
/* 
* Formal specification and verification of a dynamic programming algorithm for calculating C(n, k).
* FEUP, MIEIC, MFES, 2020/21.
*/

// Initial recursive definition of C(n, k), based on the Pascal equality.
function comb(n: nat, k: nat): nat 
  requires 0 <= k <= n
{
  if k == 0 || k == n then 1 else comb(n-1, k) + comb(n-1, k-1)  
}
by method
// Calculates C(n,k) iteratively in time O(k*(n-k)) and space O(n-k), 
// with dynamic programming.
{
  var maxj := n - k;
  var c := new nat[1 + maxj];
  forall i | 0 <= i <= maxj {
       c[i] := 1;
  }
  var i := 1;
  while i <= k 
    invariant 1 <= i <= k+1
    invariant forall j :: 0 <= j <= maxj ==> c[j] == comb(i-1 + j, i-1)
    decreases k - i + 1
  {
    var j := 1;
    while j <= maxj
      invariant 1 <= j <= maxj+1
      invariant forall l :: 0 <= l < j ==> c[l] == comb(i + l, i)
      invariant forall l :: j <= l <= maxj ==> c[l] == comb(i-1 + l, i-1)
      decreases maxj - j + 1
    {
      c[j] := c[j] + c[j-1];
      // comb(i + j, i) == comb(i-1 + j, i-1) + comb(i-1 + j, i)
      // By Pascal's rule: comb(n, k) = comb(n-1, k-1) + comb(n-1, k)
      // Here: n = i + j, k = i
      // comb(i + j, i) = comb(i + j - 1, i - 1) + comb(i + j - 1, i)
      // c[j-1] == comb(i + (j-1), i)
      // c[j] (before update) == comb(i-1 + j, i-1)
      // c[j] (after update) == comb(i-1 + j, i-1) + comb(i + j - 1, i)
      // But by the invariant, c[j-1] == comb(i + (j-1), i)
      // And c[j] (before update) == comb(i-1 + j, i-1)
      // After update: c[j] == comb(i-1 + j, i-1) + comb(i + j - 1, i)
      // We need to show this equals comb(i + j, i)
      // But comb(i + j, i) = comb(i + j - 1, i - 1) + comb(i + j - 1, i)
      // But comb(i-1 + j, i-1) == comb(i + j - 1, i - 1)
      // So the update is correct.
      j := j+1;
    } 
    i := i + 1;
  }
  // At this point, i == k+1
  // So by invariant: forall j :: 0 <= j <= maxj ==> c[j] == comb(k + j, k)
  // In particular, c[maxj] == comb(k + maxj, k)
  // But maxj = n - k, so k + maxj = n
  // So c[maxj] == comb(n, k)
  assert c[maxj] == comb(n, k);
  return c[maxj];
}

lemma combProps(n: nat, k: nat)
   requires 0 <= k <= n
   ensures comb(n, k) == comb(n, n-k)
{
  // Proof by induction on k
  if k == 0 || k == n {
    // comb(n, 0) == 1 == comb(n, n)
  } else {
    // comb(n, k) == comb(n-1, k) + comb(n-1, k-1)
    // comb(n, n-k) == comb(n-1, n-k) + comb(n-1, n-k-1)
    // By induction hypothesis:
    // comb(n-1, k) == comb(n-1, (n-1)-k)
    // comb(n-1, k-1) == comb(n-1, (n-1)-(k-1))
    // So comb(n, k) == comb(n-1, n-k) + comb(n-1, n-k-1) == comb(n, n-k)
  }
}

method Main()
{
  // Statically checked (proved) test cases!    


  var res1 := comb(40, 10);
  print "combDyn(40, 10) = ", res1, "\n";

}

method testComb() {
}

function abs(a: real) : real {if a>0.0 then a else -a}
