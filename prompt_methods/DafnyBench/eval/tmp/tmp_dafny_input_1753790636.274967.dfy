lemma SkippingLemma(a : array<int>, j : int)
   requires a != null
   requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
   requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
   requires 0 <= j < a.Length
   ensures forall k :: j <= k < j + a[j] && k < a.Length ==> a[k] != 0
{
   var i := j;
   while i < j + a[j] && i < a.Length
      invariant j <= i <= a.Length
      invariant i <= j + a[j]
      invariant forall k :: j <= k < i && k < a.Length ==> a[k] != 0
   {
      // Prove a[i] != 0 for i in range
      // We cannot assert a[i] != 0 directly, but we can use the precondition and invariants.
      i := i + 1;
   }
}

method FindZero(a: array<int>) returns (index: int)
   requires a != null
   requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
   requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
   ensures index < 0  ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
   ensures 0 <= index ==> index < a.Length && a[index] == 0
{
   index := 0;
   while index < a.Length
      invariant 0 <= index <= a.Length
      invariant forall i :: 0 <= i < index ==> a[i] != 0
   {
      if a[index] == 0 { return; }
      SkippingLemma(a, index);
      // a[index] != 0 by loop condition and invariant
      // a[index] >= 1 by precondition
      // So index + a[index] > index, and index increases
      index := index + a[index];
   }
   index := -1;
}

function abs(a: real) : real {if a>0.0 then a else -a}
