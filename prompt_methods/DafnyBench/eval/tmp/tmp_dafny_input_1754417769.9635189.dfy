// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class SumOfCubes {
  static function SumEmUp(n: int, m: int): int
    requires 0 <= n && n <= m;
    decreases m - n;
  {
    if m == n then 0 else n*n*n + SumEmUp(n+1, m)
  }

  static method Socu(n: int, m: int) returns (r: int)
    requires 0 <= n && n <= m;
    ensures r == SumEmUp(n, m);
  {
    var a := SocuFromZero(m);
    var b := SocuFromZero(n);
    r := a - b;
    Lemma0(n, m);
  }

  static method SocuFromZero(k: int) returns (r: int)
    requires 0 <= k;
    ensures r == SumEmUp(0, k);
  {
    var g := Gauss(k);
    r := g * g;
    Lemma1(k);
  }

  ghost static method Lemma0(n: int, m: int)
    requires 0 <= n && n <= m;
    ensures SumEmUp(n, m) == SumEmUp(0, m) - SumEmUp(0, n);
  {
    // Prove by induction on m-n
    if n == m {
      // SumEmUp(n, m) == 0 == SumEmUp(0, m) - SumEmUp(0, n)
      assert SumEmUp(n, m) == SumEmUp(0, m) - SumEmUp(0, n);
    } else {
      Lemma0(n+1, m);
      assert SumEmUp(n, m) == n*n*n + SumEmUp(n+1, m);
      assert SumEmUp(n+1, m) == SumEmUp(0, m) - SumEmUp(0, n+1);
      assert SumEmUp(n, m) == n*n*n + SumEmUp(0, m) - SumEmUp(0, n+1);
      assert SumEmUp(0, n+1) == SumEmUp(0, n) + n*n*n;
      assert SumEmUp(n, m) == n*n*n + SumEmUp(0, m) - (SumEmUp(0, n) + n*n*n);
      assert SumEmUp(n, m) == SumEmUp(0, m) - SumEmUp(0, n);
    }
  }

  static function GSum(k: int): int
    requires 0 <= k;
    decreases k;
  {
    if k == 0 then 0 else GSum(k-1) + k-1
  }

  static method Gauss(k: int) returns (r: int)
    requires 0 <= k;
    ensures r == GSum(k);
  {
    r := k * (k - 1) / 2;
    Lemma2(k);
  }

  ghost static method Lemma1(k: int)
    requires 0 <= k;
    ensures SumEmUp(0, k) == GSum(k) * GSum(k);
  {
    // Prove by induction on k
    if k == 0 {
      assert SumEmUp(0, 0) == 0;
      assert GSum(0) == 0;
    } else {
      Lemma1(k-1);
      Lemma2(k);
      assert SumEmUp(0, k) == SumEmUp(0, k-1) + (k-1)*(k-1)*(k-1);
      assert GSum(k) == GSum(k-1) + k-1;
      assert SumEmUp(0, k-1) == GSum(k-1) * GSum(k-1);
      assert SumEmUp(0, k) == GSum(k-1) * GSum(k-1) + (k-1)*(k-1)*(k-1);
      assert SumEmUp(0, k) == (GSum(k-1) + k-1) * (GSum(k-1) + k-1);
      assert SumEmUp(0, k) == GSum(k) * GSum(k);
    }
  }

  ghost static method Lemma2(k: int)
    requires 0 <= k;
    ensures 2 * GSum(k) == k * (k - 1);
  {
    // Prove by induction on k
    if k == 0 {
      assert GSum(0) == 0;
    } else {
      Lemma2(k-1);
      assert 2 * GSum(k-1) == (k-1) * (k-2);
      assert GSum(k) == GSum(k-1) + k-1;
      assert 2 * GSum(k) == 2 * (GSum(k-1) + k-1);
      assert 2 * GSum(k) == 2 * GSum(k-1) + 2 * (k-1);
      assert 2 * GSum(k) == (k-1)*(k-2) + 2*(k-1);
      assert (k-1)*(k-2) + 2*(k-1) == (k-1)*((k-2)+2);
      assert (k-1)*((k-2)+2) == (k-1)*k;
      assert 2 * GSum(k) == k*(k-1);
    }
  }

  static function SumEmDown(n: int, m: int): int
    requires 0 <= n && n <= m;
    decreases m - n;
  {
    if m == n then 0 else SumEmDown(n, m-1) + (m-1)*(m-1)*(m-1)
  }

  ghost static method Lemma3(n: int, m: int)
    requires 0 <= n && n <= m;
    ensures SumEmUp(n, m) == SumEmDown(n, m);
  {
    // Prove by induction on m-n
    if n == m {
      assert SumEmUp(n, m) == 0;
      assert SumEmDown(n, m) == 0;
    } else {
      Lemma3(n+1, m);
      assert SumEmUp(n, m) == n*n*n + SumEmUp(n+1, m);
      assert SumEmDown(n, m) == SumEmDown(n+1, m) + n*n*n;
      assert SumEmUp(n+1, m) == SumEmDown(n+1, m);
      assert SumEmUp(n, m) == n*n*n + SumEmDown(n+1, m);
      assert SumEmDown(n, m) == n*n*n + SumEmDown(n+1, m);
      assert SumEmUp(n, m) == SumEmDown(n, m);
    }
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
