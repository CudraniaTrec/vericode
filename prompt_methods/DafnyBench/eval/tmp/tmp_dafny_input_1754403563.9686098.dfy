
// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// A Dafny rendition of an F* version of QuickSort (included at the bottom of this file).
// Unlike the F* version, Dafny also proves termination and does not use any axioms.  However,
// Dafny needs help with a couple of lemmas in places where F* does not need them.
// Comments below show differences between the F* and Dafny versions.

datatype List<T> = Nil | Cons(T, List)

function length(list: List): nat  // for termination proof
{
  match list
  case Nil => 0
  case Cons(_, tl) => 1 + length(tl)
}

// In(x, list) returns the number of occurrences of x in list
function In(x: int, list: List<int>): nat
{
  match list
  case Nil => 0
  case Cons(y, tl) => (if x == y then 1 else 0) + In(x, tl)
}

predicate SortedRange(m: int, n: int, list: List<int>)
{
  match list
  case Nil => m <= n
  case Cons(hd, tl) => m <= hd <= n && SortedRange(hd, n, tl)
}

function append(n0: int, n1: int, n2: int, n3: int, i: List<int>, j: List<int>): List<int>
  requires n0 <= n1 <= n2 <= n3
  requires SortedRange(n0, n1, i) && SortedRange(n2, n3, j)
  ensures SortedRange(n0, n3, append(n0, n1, n2, n3, i, j))
  ensures forall x :: In(x, append(n0, n1, n2, n3, i, j)) == In(x, i) + In(x, j)
{
  match i
  case Nil => j
  case Cons(hd, tl) =>
    // strongest possible annotation:
    // hd : n0 <= hd <= n1
    // SortedRange(hd, n1, tl)
    // SortedRange(n2, n3, j)
    // n0 <= hd <= n1 <= n2 <= n3
    // append(hd, n1, n2, n3, tl, j) is SortedRange(hd, n3, ...)
    // Cons(hd, ...) is SortedRange(n0, n3, ...)
    assert n0 <= hd <= n1;
    assert SortedRange(hd, n1, tl);
    assert SortedRange(n2, n3, j);
    assert n1 <= n2;
    assert n0 <= hd <= n1 <= n2 <= n3;
    Cons(hd, append(hd, n1, n2, n3, tl, j))
}

function partition(x: int, l: List<int>): (List<int>, List<int>)
  ensures var (lo, hi) := partition(x, l);
    (forall y :: In(y, lo) == if y <= x then In(y, l) else 0) &&
    (forall y :: In(y, hi) == if x < y then In(y, l) else 0) &&
    length(l) == length(lo) + length(hi)  // for termination proof
{
  match l
  case Nil =>
    assert forall y :: In(y, Nil) == 0;
    (Nil, Nil)
  case Cons(hd, tl) =>
    var (lo, hi) := partition(x, tl);
    // strongest possible annotation:
    // For all y:
    //   In(y, lo) == if y <= x then In(y, tl) else 0
    //   In(y, hi) == if x < y then In(y, tl) else 0
    //   length(tl) == length(lo) + length(hi)
    assert length(l) == 1 + length(tl);
    if hd <= x then
      // lo' = Cons(hd, lo), hi' = hi
      // In(y, Cons(hd, lo)) == (if y == hd then 1 else 0) + In(y, lo)
      // In(y, lo') == if y <= x then (if y == hd then 1 else 0) + In(y, tl) else 0
      assert In(hd, Cons(hd, lo)) == 1 + In(hd, lo);
      assert In(hd, lo) == if hd <= x then In(hd, tl) else 0;
      assert In(hd, lo) == In(hd, tl); // since hd <= x
      assert In(hd, Cons(hd, lo)) == 1 + In(hd, tl);
      assert length(lo) + 1 + length(hi) == length(l);
      (Cons(hd, lo), hi)
    else
      // lo' = lo, hi' = Cons(hd, hi)
      // In(y, Cons(hd, hi)) == (if y == hd then 1 else 0) + In(y, hi)
      // In(y, hi') == if x < y then (if y == hd then 1 else 0) + In(y, tl) else 0
      assert In(hd, Cons(hd, hi)) == 1 + In(hd, hi);
      assert In(hd, hi) == if x < hd then In(hd, tl) else 0;
      assert In(hd, hi) == In(hd, tl); // since x < hd
      assert In(hd, Cons(hd, hi)) == 1 + In(hd, tl);
      assert length(lo) + length(hi) + 1 == length(l);
      (lo, Cons(hd, hi))
}

function sort(min: int, max: int, i: List<int>): List<int>
  requires min <= max
  requires forall x :: In(x, i) != 0 ==> min <= x <= max
  ensures SortedRange(min, max, sort(min, max, i))
  ensures forall x :: In(x, i) == In(x, sort(min, max, i))
{
  match i
  case Nil =>
    assert SortedRange(min, max, Nil);
    assert forall x :: In(x, Nil) == 0;
    Nil
  case Cons(hd, tl) =>
    // strongest possible annotation:
    // min <= hd <= max
    // forall x :: In(x, tl) != 0 ==> min <= x <= max
    assert min <= hd <= max;
    var (lo, hi) := partition(hd, tl);
    // lo: all elements <= hd, hi: all elements > hd
    // forall x :: In(x, lo) == if x <= hd then In(x, tl) else 0
    // forall x :: In(x, hi) == if hd < x then In(x, tl) else 0
    var i' := sort(min, hd, lo);
    var j' := sort(hd, max, hi);
    // i' is SortedRange(min, hd, i')
    // j' is SortedRange(hd, max, j')
    // append(min, hd, hd, max, i', Cons(hd, j')) is SortedRange(min, max, ...)
    assert SortedRange(min, hd, i');
    assert SortedRange(hd, max, j');
    assert SortedRange(hd, max, Cons(hd, j'));
    assert SortedRange(min, max, append(min, hd, hd, max, i', Cons(hd, j')));
    // For all x, In(x, i) == In(x, append(...))
    // In(x, i) == (if x == hd then 1 else 0) + In(x, tl)
    // In(x, append(...)) == In(x, i') + In(x, Cons(hd, j'))
    // In(x, i') == In(x, lo)
    // In(x, Cons(hd, j')) == (if x == hd then 1 else 0) + In(x, j')
    // In(x, j') == In(x, hi)
    // In(x, lo) + (if x == hd then 1 else 0) + In(x, hi) == (if x == hd then 1 else 0) + In(x, tl)
    assert forall x :: In(x, i) == In(x, append(min, hd, hd, max, i', Cons(hd, j')));
    append(min, hd, hd, max, i', Cons(hd, j'))
}

/*
module Sort

type SortedRange : int => int => list int => E
assume Nil_Sorted : forall (n:int) (m:int). n <= m <==> SortedRange n m []
assume Cons_Sorted: forall (n:int) (m:int) (hd:int) (tl:list int).
               SortedRange hd m tl && (n <= hd) && (hd <= m)
          <==> SortedRange n m (hd::tl)

val append: n1:int -> n2:int{n1 <= n2} -> n3:int{n2 <= n3} -> n4:int{n3 <= n4}
         -> i:list int{SortedRange n1 n2 i}
         -> j:list int{SortedRange n3 n4 j}
         -> k:list int{SortedRange n1 n4 k
                      /\ (forall x. In x k <==> In x i \/ In x j)}
let rec append n1 n2 n3 n4 i j = match i with
  | [] ->
    (match j with
      | [] -> j
      | _::_ -> j)
  | hd::tl -> hd::(append hd n2 n3 n4 tl j)

val partition: x:int
            -> l:list int
            -> (lo:list int
                * hi:list int{(forall y. In y lo ==> y <= x /\ In y l)
                               /\ (forall y. In y hi ==> x < y /\ In y l)
                               /\ (forall y. In y l ==> In y lo \/ In y hi)})
let rec partition x l = match l with
  | [] -> ([], [])
  | hd::tl ->
    let lo, hi = partition x tl in
    if hd <= x
    then (hd::lo, hi)
    else (lo, hd::hi)

val sort: min:int
       -> max:int{min <= max}
       -> i:list int {forall x. In x i ==> (min <= x /\ x <= max)}
       -> j:list int{SortedRange min max j /\ (forall x. In x i <==> In x j)}
let rec sort min max i = match i with
  | [] -> []
  | hd::tl ->
    let lo,hi = partition hd tl in
    let i' = sort min hd lo in
    let j' = sort hd max hi in
    append min hd hd max i' (hd::j')

*/

function abs(a: real) : real {if a>0.0 then a else -a}
