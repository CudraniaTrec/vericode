class BoundedQueue<T(0)>
{
 // abstract state
 ghost var contents: seq<T> // the contents of the bounded queue
 ghost var N: nat // the (maximum) size of the bounded queue
 ghost var Repr: set<object>
 // concrete state
 var data: array<T>
 var wr: nat
 var rd: nat

 ghost predicate Valid()
   reads this, Repr
   ensures Valid() ==> this in Repr && |contents| <= N 
 {
   this in Repr && data in Repr &&
   data.Length == N + 1 &&
   wr <= N && rd <= N &&
   contents == if rd <= wr then data[rd..wr] else data[rd..] + data[..wr]
 }

 constructor (N: nat)
   ensures Valid() && fresh(Repr)
   ensures contents == [] && this.N == N
 {
   contents := [];
   this.N := N;
   data := new T[N+1]; // requires T to have default initial value
   rd, wr := 0, 0;
   Repr := {this, data};
   // No assert Valid() here due to Dafny constructor restrictions
 }

 method Insert(x:T)
   requires Valid()
   requires |contents| != N
   modifies Repr
   ensures contents == old(contents) + [x]
   ensures N == old(N)
   ensures Valid() && fresh(Repr - old(Repr))
 {
   // Loop-free, so no loop invariants needed
   // Strongest assertions about state transitions
   contents := old(contents) + [x];

   data[wr] := x;
   assert forall i :: 0 <= i < |old(contents)| ==>
     (if rd <= wr then old(contents)[i] == data[rd + i]
      else if rd + i < data.Length then old(contents)[i] == data[rd + i]
      else old(contents)[i] == data[(rd + i) % data.Length]);
   if wr == data.Length - 1 {
     wr := 0;
   } else {
     wr := wr + 1;
   }
   assert |contents| <= N;
   assert N == old(N);
   assert Valid();
   assert fresh(Repr - old(Repr));
 }

 method Remove() returns (x:T)
   requires Valid()
   requires |contents| != 0
   modifies Repr
   ensures contents == old(contents[1..]) && old(contents[0]) == x
   ensures N == old(N)
   ensures Valid() && fresh(Repr - old(Repr))
 {
   // Loop-free, so no loop invariants needed
   // Strongest assertions about state transitions
   x := data[rd];
   contents := contents[1..];
   if rd == data.Length - 1 {
     rd := 0;
   } else {
     rd := rd + 1;
   }
   assert N == old(N);
   assert Valid();
   assert fresh(Repr - old(Repr));
 }
}
function abs(a: real) : real {if a>0.0 then a else -a}
