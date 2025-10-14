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
    invariant (forall e: T :: multiset(r)[e] == multiset(s1[..i])[e] if f(e) else 0)
  {
    if f(s1[i]) {
      r := r + [s1[i]];
    }
    i := i + 1;
  }
}

method Main(s1: seq<T>)
{
   var r1, r2: seq<T>;

   r1 := Select(s1);
   r2 := Select(s1);


}

function abs(a: real) : real {if a>0.0 then a else -a}
