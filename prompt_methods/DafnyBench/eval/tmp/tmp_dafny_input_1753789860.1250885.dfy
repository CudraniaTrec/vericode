
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
   assert Valid();
 }

 method Insert(x:T)
   requires Valid()
   requires |contents| != N
   modifies Repr
   ensures contents == old(contents) + [x]
   ensures N == old(N)
   ensures Valid() && fresh(Repr - old(Repr))
 {
   // Strongest annotation: contents grows by one, N unchanged, Valid preserved
   var old_wr := wr;
   var old_rd := rd;
   var old_contents := contents;
   var old_data := data[..];
   contents := old(contents) + [x];

   data[wr] := x;
   assert forall i :: 0 <= i < |old_contents| ==> 
     (if old_rd <= old_wr then 
       old_contents[i] == data[old_rd + i] 
     else 
       if old_rd + i < data.Length then 
         old_contents[i] == data[old_rd + i] 
       else 
         old_contents[i] == data[(old_rd + i) % data.Length]);
   assert (wr != data.Length - 1 ==> contents == if rd <= wr+1 then data[rd..wr+1] else data[rd..] + data[..wr+1]);
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
   // Strongest annotation: contents shrinks by one, N unchanged, Valid preserved
   var old_wr := wr;
   var old_rd := rd;
   var old_contents := contents;
   var old_data := data[..];
   assert |contents| > 0;
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
