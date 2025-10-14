predicate recSorted(s : string) decreases s
{    
    if (|s| <=1) then true else if(s[0] > s[1]) then false else recSorted(s[1..])
}

predicate forallSorted (s : string)
{ 
    forall x,y::0<x<y<|s| ==> s[x]<s[y]
}

lemma forallEQrec(a:string)
ensures forallSorted(a) == recSorted(a) {
    if |a| <= 1 {
        assert forallSorted(a);
        assert recSorted(a);
    } else {
        if a[0] > a[1] {
            assert !recSorted(a);
            assert !forallSorted(a);
        } else {
            forallEQrec(a[1..]);
        }
    }
}
        
method whileSorted(a:string) returns (r : bool) 
ensures r == forallSorted(a) // ONEOF
//ensures r == recSorted(a)    // ONEOF

{
    var i := 1;
    r := true;
    if |a| <=1 {
        return true;
    }
    while i <|a| 
    invariant 0 < i <= |a|
    invariant r == forallSorted(a[..i])
    decreases |a| -i {
        if a[i-1] > a[i] {
            r:= false;
        } 
        i := i+1;
    }
}

lemma SortedSumForall(a:string,b:string)
  requires forallSorted(a)
  requires forallSorted(b)
  ensures forallSorted(a + b) 
  requires (|a| >0 && |b| >0 ) ==> a[|a|-1] <= b[0]
{
    assert forall x, y :: 0 < x < y < |a| ==> (a + b)[x] < (a + b)[y];
    assert forall x, y :: |a| <= x < y < |a| + |b| ==> (a + b)[x] < (a + b)[y];
    if |a| > 0 && |b| > 0 {
        assert forall x, y :: 0 < x < |a| && |a| <= y < |a| + |b| ==> a[x] < b[y - |a|];
    }
}

lemma SortedSumRec(a:string,b:string)
  requires recSorted(a)
  requires recSorted(b)
  requires |a| > 0 && |b| > 0
  requires a[|a|-1] <= b[0]
  ensures recSorted(a + b)
{
    forallEQrec(a);
    forallEQrec(b);
    forallEQrec(a+b);
    SortedSumForall(a, b);
}

lemma SortedSumInduction(a:string,b:string)
  requires recSorted(a)
  requires recSorted(b)
  requires |a| > 0 && |b| > 0
  requires a[|a|-1] <= b[0]
  ensures recSorted(a + b)
{        
    if |a| < 2 {
        assert recSorted(a + b);
    } else {
        assert recSorted(a[1..]);
        SortedSumInduction(a[1..],b);
        assert recSorted(a[1..] + b);
        assert [a[0]] + a[1..] == a;
        assert recSorted([a[0]] + a[1..]);
        assert [a[0]] + (a[1..] + b) == ([a[0]] + a[1..]) + b;
        assert recSorted(a+b);
    }
}

lemma VowelsLemma(s : string, t : string) 
  ensures vowels(s + t) == vowels(s) + vowels(t) 
{
    if |s| == 0 {
        assert vowels(s + t) == vowels(t);
        assert vowels(s) == 0;
        assert vowels(s) + vowels(t) == vowels(t);
    } else {
        assert [s[0]] + s[1..] == s;
        assert [s[0]] + (s[1..] + t) == ([s[0]] + s[1..]) + t;
        if s[0] in "aeiou" {
            assert vowels(s) == 1 + vowels(s[1..]);
            assert vowels(s + t) == 1 + vowels(s[1..] + t);
            VowelsLemma(s[1..], t);
            assert vowels(s[1..] + t) == vowels(s[1..]) + vowels(t);
            assert vowels(s + t) == 1 + vowels(s[1..]) + vowels(t);
            assert vowels(s) + vowels(t) == (1 + vowels(s[1..])) + vowels(t);
        } else {
            assert vowels(s) == vowels(s[1..]);
            assert vowels(s + t) == vowels(s[1..] + t);
            VowelsLemma(s[1..], t);
            assert vowels(s + t) == vowels(s[1..]) + vowels(t);
            assert vowels(s) + vowels(t) == vowels(s[1..]) + vowels(t);
        }
    }
}

function vowels(s : string) : (r : nat)
{
    if (|s| == 0) then 0
      else 
       (if (s[0] in "aeiou") then 1 else 0)
         + vowels(s[1..])
}

function vowelsF(s : string) : nat {
  var m := multiset(s);
  m['a'] + m['e'] + m['i'] + m['o'] + m['u']
}

lemma VowelsLemmaF(s : string, t : string) 
  ensures vowelsF(s + t) == vowelsF(s) + vowelsF(t) 
{
}

datatype StackModel = Empty | Push(value : int, prev : StackModel)

class Stack {
   var values : array<int>;
   var capacity : nat;
   var size : nat;
   var Repr : set<object>;

predicate Valid()
   reads Repr
{
this in Repr && values in Repr && size <= values.Length && values.Length == capacity
} 

constructor(capacity_ : nat) 
ensures capacity == capacity_
ensures Valid()
ensures values.Length == capacity_
ensures values.Length == capacity
ensures size ==0
ensures forall i:nat::i<values.Length ==>values[i] ==0{
   capacity := capacity_;
   values := new int[capacity_](x=>0);
   size := 0;
   Repr := {this,values};
}

function toStackModel() : StackModel 
  reads Repr
  requires Valid()
{
    toStackModelAux(size)
}

function toStackModelAux(i : nat) : StackModel 
reads Repr
requires Valid()
decreases i
{
    if i == 0 then Empty else Push(values[i-1], toStackModelAux(i-1))
}

method push(i : int) 
  requires Valid()
  ensures Valid()
  modifies Repr
  ensures capacity == old(capacity)
{
    values[size] := i;
    size := size + 1;
}

method pop() returns (r : int) 
    requires Valid()
    modifies this`size;
    ensures Valid();
{
    r := values[size-1];
    size := size - 1;
}

function top() : (r : int)
   requires Valid()
   reads Repr
   ensures Valid();
{
    values[size-1]
}
}

method StackOK(s : Stack, i : int, j : int)
 requires s.Valid()
 requires 0 <= s.size < (s.capacity - 2)
 requires s.values.Length == s.capacity
 requires s.size == 0
 requires s.capacity > 2
 modifies s.Repr
{
  var sSM := s.toStackModel();
  assert s.size == 0;
  assert sSM.Empty?;
  s.push(i);
  assert s.toStackModel() == Push(i,sSM);
  var v := s.pop();
  assert v == i;
  assert s.toStackModel() == sSM;
  s.push(i);
  assert s.toStackModel() == Push(i,sSM);
  assert Push(i,sSM).prev == sSM;
  s.push(j);
  assert s.toStackModel() == Push(j,Push(i,sSM));
  v := s.top();
  assert v == j;
  v := s.pop();
  assert v == j;
  assert s.toStackModel() == Push(i,sSM);
  v := s.pop();
  assert v == i;    
}

function abs(a: real) : real {if a>0.0 then a else -a}
