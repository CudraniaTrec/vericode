/**
 * Proves the correctness of a "raw" array sorting algorithm that swaps elements out of order, chosen randomly.
 * FEUP, MFES, 2020/21.
 */

// Type of each array element; can be any type supporting comparision operators.
type T = int 

// Checks if array 'a' is sorted by non-descending order.
ghost predicate sorted(a: array<T>)
  reads a
{ forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j] }

// Obtains the set of all inversions in an array 'a', i.e., 
// the pairs of indices i, j such that i < j and a[i] > a[j]. 
ghost function inversions(a: array<T>): set<(nat, nat)>
  reads a
{ set i, j | 0 <= i < j < a.Length && a[i] > a[j] :: (i, j) }

// Sorts an array by simply swapping elements out of order, chosen randomly.
method rawsort(a: array<T>)
   modifies a
   ensures sorted(a) && multiset(a[..]) == multiset(old(a[..]))
{
   // Strongest annotation: the number of inversions strictly decreases at each recursive call.
   // The multiset of array elements is preserved.
   // When no inversions remain, the array is sorted.
   // Loop invariant is not needed as this is a recursive method, but we use assertions and ghost code.

   if i, j :| 0 <= i < j < a.Length && a[i] > a[j]  {
      ghost var bef := inversions(a); // inversions before swapping
      assert (i, j) in bef;
      a[i], a[j] := a[j], a[i]; // swap
      ghost var aft := inversions(a); // inversions after swapping  
      assert |aft| < |bef|; // the number of inversions strictly decreases
      assert multiset(a[..]) == multiset(old(a[..]));
      ghost var aft2bef := map p | p in aft :: // maps inversions in 'aft' to 'bef'
                  (if p.0 == i && p.1 > j then j else if p.0 == j then i else p.0,
                   if p.1 == i then j else if p.1 == j && p.0 < i then i else p.1);    
      // The mappingProp lemma is used to show |aft| < |bef| via injectivity and non-surjectivity.
      mappingProp(aft, bef, (i, j), aft2bef); // recall property implying |aft| < |bef|
      rawsort(a); // proceed recursivelly
   } else {
      // No inversions left, so the array is sorted.
      assert inversions(a) == {};
      assert sorted(a);
   }
}

// States and proves (by induction) the following property: given sets 'a' and 'b' and an injective
// and non-surjective mapping 'm' from elements in 'a' to elements in 'b', then |a| < |b|.
// To facilitate the proof, it is given an element 'k' in 'b' that is not an image of elements in 'a'.   
lemma mappingProp<T1, T2>(a: set<T1>, b: set<T2>, k: T2, m: map<T1, T2>)
  requires k in b
  requires forall x :: x in a ==> x in m && m[x] in b - {k} 
  requires forall x, y :: x in a && y in a && x != y ==> m[x] != m[y] 
  ensures |a| < |b|
{
   if x :| x in a {
      // Strongest invariant: |a| < |b| is preserved by induction.
      assert m[x] in b - {k};
      assert forall y :: y in a - {x} && y != x ==> m[y] != m[x];
      mappingProp(a - {x}, b - {m[x]}, k, m);
   } else {
      // Base case: a is empty, so |a| = 0 < |b| (since k in b, so |b| >= 1)
      assert |a| == 0;
      assert |b| >= 1;
   }
}

method testRawsort() {
   var a : array<T> := new T[] [3, 5, 1]; 
   rawsort(a);
}

function abs(a: real) : real {if a>0.0 then a else -a}
