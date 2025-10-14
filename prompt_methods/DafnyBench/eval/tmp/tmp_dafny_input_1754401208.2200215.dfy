// RUN: %dafny /compile:3 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// /autoTriggers:1 added to suppress instabilities

method Main() { }

method H(a: array<int>, c: array<int>, n: nat, j: nat)
  requires j < n == a.Length == c.Length
{
  var A := a[..];
  var C := c[..];

  if {
    case A[j] == C[j] =>
      assert 0 <= j < n;
      assert A[j] == C[j];
    case forall i :: 0 <= i < n ==> A[i] == C[i] =>
      assert forall i {:trigger A[i], C[i]} :: 0 <= i < n ==> A[i] == C[i];
    case forall i :: 0 <= i < n ==> A[i] == C[i] =>
      assert forall i {:trigger A[i], C[i]} :: 0 <= i < n ==> A[i] == C[i];
    case A == C =>
      assert A == C;
    case A == C =>
      assert A == C;
    case true =>
      assert true;
  }
}

method K(a: array<int>, c: array<int>, n: nat)
  requires n <= a.Length && n <= c.Length
{
  var A := a[..n];
  var C := c[..n];
  if {
    case A == C =>
      assert A == C;
    case A == C =>
      assert A == C;
    case true =>
      assert true;
  }
}

method L(a: array<int>, c: array<int>, n: nat)
  requires n <= a.Length == c.Length
{
  var A := a[n..];
  var C := c[n..];
  var h := a.Length - n;
  if {
    case A == C =>
      assert A == C;
    case A == C =>
      assert A == C;
    case true =>
      assert true;
  }
}

method M(a: array<int>, c: array<int>, m: nat, n: nat, k: nat, l: nat)
  requires k + m <= a.Length
  requires l + n <= c.Length
{
  var A := a[k..k+m];
  var C := c[l..l+n];
  if A == C {
    if * {
      assert m == n;
      assert forall i {:trigger A[i], C[i]} :: 0 <= i < m ==> a[k + i] == c[l + i];
    } else if * {
      assert m == n;
      assert forall i {:trigger A[i], C[i]} :: 0 <= i < m ==> a[k + i] == c[l + i];
    } else if * {
      assert m == n;
      assert forall i {:trigger A[i], C[i]} :: 0 <= i < m ==> a[k + i] == c[l + i];
    } else if * {
      assert m == n;
      assert forall i {:trigger A[i], C[i]} :: 0 <= i < m ==> a[k + i] == c[l + i];
    } else if * {
      assert m == n;
      assert forall i {:trigger A[i], C[i]} :: 0 <= i < m ==> a[k + i] == c[l + i];
    } else if * {
      assert m == n;
      assert forall i {:trigger A[i], C[i]} :: 0 <= i < m ==> a[k + i] == c[l + i];
    }
  }
}

method M'(a: array<int>, c: array<int>, m: nat, n: nat, k: nat, l: nat)
  requires k + m <= a.Length
  requires l + n <= c.Length
{
  if {
    case l+m <= c.Length && forall i :: 0 <= i < m ==> a[i] == c[l+i] =>
      assert l + m <= c.Length;
      assert forall i {:trigger a[i], c[l + i]} :: 0 <= i < m ==> a[i] == c[l + i];
    case l+a.Length <= c.Length && forall i :: k <= i < a.Length ==> a[i] == c[l+i] =>
      assert l + a.Length <= c.Length;
      assert forall i {:trigger a[i], c[l + i]} :: k <= i < a.Length ==> a[i] == c[l + i];
    case l+k+m <= c.Length && forall i :: k <= i < k+m ==> a[i] == c[l+i] =>
      assert l + k + m <= c.Length;
      assert forall i {:trigger a[i], c[l + i]} :: k <= i < k + m ==> a[i] == c[l + i];
    case true =>
      assert true;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
