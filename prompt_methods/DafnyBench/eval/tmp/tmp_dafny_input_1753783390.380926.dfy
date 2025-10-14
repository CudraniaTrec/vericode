method LinearSearch3<T>(a: array<T>, P: T -> bool) returns (n: int)
  requires exists i :: 0 <= i < a.Length && P(a[i])
  ensures 0 <= n < a.Length && P(a[n])
  ensures forall k :: 0 <= k < n ==> !P(a[k])
{
  n := 0;
  while true
    invariant 0 <= n <= a.Length
    invariant forall k :: 0 <= k < n ==> !P(a[k])
    invariant exists i :: n <= i < a.Length && P(a[i])
    decreases a.Length - n
  {
    if P(a[n]) {
      assert 0 <= n < a.Length;
      assert P(a[n]);
      assert forall k :: 0 <= k < n ==> !P(a[k]);
      return;
    }
    n := n + 1;
  }
}
function abs(a: real) : real {if a>0.0 then a else -a}
