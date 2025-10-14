// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type T
function f(a: T) : bool

method Select(s1: seq<T>) returns (r: seq<T>)
  ensures (forall e: T  :: f(e) ==> multiset(s1)[e] == multiset(r)[e])
  ensures (forall e: T  :: (!f(e)) ==> 0 == multiset(r)[e])
{
  var i: int := 0;
  r := [];
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant |r| <= i
    invariant (forall e: T :: multiset(r)[e] == |set j: int | 0 <= j < i && f(s1[j]) && s1[j] == e|)
  {
    if f(s1[i]) {
      r := r + [s1[i]];
    }
    i := i + 1;
  }
  // At loop exit, i == |s1|
  // So for all e, multiset(r)[e] == number of j in 0..|s1|-1 with f(s1[j]) and s1[j]==e
  // That is, for all e, multiset(r)[e] == |set j: int | 0 <= j < |s1| && f(s1[j]) && s1[j]==e|
  // For e with f(e): multiset(s1)[e] == number of j with s1[j]==e
  // But we only count those j where f(s1[j]), so for f(e), multiset(r)[e] == multiset(s1)[e] if f(e), else 0
  // For e with !f(e): multiset(r)[e] == 0
}

method Main(s1: seq<T>)
{
   var r1, r2: seq<T>;

   r1 := Select(s1);
   r2 := Select(s1);


}
function abs(a: real) : real {if a>0.0 then a else -a}
