
/**
  This ADT represents a multiset.
 */
trait MyMultiset {

  // internal invariant
  ghost predicate Valid()
    reads this

  // abstract variable
  ghost var theMultiset: multiset<int>

  method Add(elem: int) returns (didChange: bool)
    modifies this
    requires Valid()
    ensures Valid()
    ensures theMultiset == old(theMultiset) + multiset{elem}
    ensures didChange

  ghost predicate Contains(elem: int)
    reads this
  { elem in theMultiset }

  method Remove(elem: int) returns (didChange: bool)
    modifies this
    requires Valid()
    ensures Valid()
    /* If the multiset contains the element */
    ensures old(Contains(elem)) ==> theMultiset == old(theMultiset) - multiset{elem}
    ensures old(Contains(elem)) ==> didChange
    /* If the multiset does not contain the element */
    ensures ! old(Contains(elem)) ==> theMultiset == old(theMultiset)
    ensures ! old(Contains(elem)) ==> ! didChange

  method Length() returns (len: int)
    requires Valid()
    ensures Valid()
    ensures len == |theMultiset|

  method equals(other: MyMultiset) returns (equal?: bool)
    requires Valid()
    requires other.Valid()
    ensures Valid()
    ensures equal? <==> theMultiset == other.theMultiset

  method getElems() returns (elems: seq<int>)
    requires Valid()
    ensures Valid()
    ensures multiset(elems) == theMultiset
}

/**
This implementation implements the ADT with a map.
 */
class MultisetImplementationWithMap extends MyMultiset {

  // valid invariant predicate of the ADT implementation
  ghost predicate Valid()
    reads this
  {
    (forall i | i in elements.Keys :: elements[i] > 0) && (theMultiset == A(elements)) && (forall i :: i in elements.Keys <==> Contains(i))
  }

  // the abstraction function
  function A(m: map<int, nat>): (s:multiset<int>)
    ensures (forall i | i in m :: m[i] == A(m)[i]) && (m == map[] <==> A(m) == multiset{}) && (forall i :: i in m <==> i in A(m))
  {
    multiset(SeqFromMap(m))
  }

  // lemma for the opposite of the abstraction function
  lemma LemmaReverseA(m: map<int, nat>, s : seq<int>)
    requires (forall i | i in m :: m[i] == multiset(s)[i]) && (m == map[] <==> multiset(s) == multiset{})
    ensures A(m) == multiset(s)
  {
  }

  // ADT concrete implementation variable
  var elements: map<int, nat>;

  // constructor of the implementation class that ensures the implementation invariant
  constructor MultisetImplementationWithMap()
    ensures Valid()
    ensures elements == map[]
    ensures theMultiset == multiset{}
  {
    elements := map[];
    theMultiset := multiset{};
    assert Valid();
  }
//adds an element to the multiset
  method Add(elem: int) returns (didChange: bool)
    modifies this
    requires Valid()
    ensures elem in elements ==> elements == elements[elem := elements[elem]]
    ensures theMultiset == old(theMultiset) + multiset{elem}
    ensures !(elem in elements) ==> elements == elements[elem := 1]
    ensures didChange
    ensures Contains(elem)
    ensures Valid()
  {
    if !(elem in elements) {
      elements := elements[elem := 1];
      assert elements[elem] == 1;
      assert forall i | i in elements.Keys :: elements[i] > 0;
    } else {
      elements := elements[elem := (elements[elem] + 1)];
      assert elements[elem] > 0;
    }

    didChange := true;

    theMultiset := A(elements);
    assert theMultiset == old(theMultiset) + multiset{elem};
    assert Valid();
    assert Contains(elem);
  }

//removes an element from the multiset
  method Remove(elem: int) returns (didChange: bool)
    modifies this
    requires Valid()
    ensures Valid()
   /* If the multiset contains the element */
    ensures old(Contains(elem)) ==> theMultiset == old(theMultiset) - multiset{elem}
    ensures old(Contains(elem)) ==> didChange
    /* If the multiset does not contain the element */
    ensures ! old(Contains(elem)) ==> theMultiset == old(theMultiset)
    ensures ! old(Contains(elem)) ==> ! didChange
    ensures didChange <==> elements != old(elements)
  {
    if elem !in elements {
      didChange := false;
      assert theMultiset == old(theMultiset);
      assert !old(Contains(elem));
      assert elements == old(elements);
      assert Valid();
      return;
    }

    assert elem in elements;
    assert elements[elem] > 0;

    elements := elements[elem := elements[elem] - 1];

    if(elements[elem] == 0) {
      elements := elements - {elem};
      assert elem !in elements;
    } else {
      assert elements[elem] > 0;
    }

    theMultiset := A(elements);
    didChange := true;
    assert theMultiset == old(theMultiset) - multiset{elem};
    assert Valid();
  }

//gets the length of the multiset
  method Length() returns (len: int)
    requires Valid()
    ensures len == |theMultiset|
  {
    var result := Map2Seq(elements);
    assert multiset(result) == theMultiset;
    len := |result|;
    assert len == |theMultiset|;
  }

//compares the current multiset with another multiset and determines if they're equal
  method equals(other: MyMultiset) returns (equal?: bool)
    requires Valid()
    requires other.Valid()
    ensures Valid()
    ensures equal? <==> theMultiset == other.theMultiset
  {
    var otherMapSeq := other.getElems();
    var c := this.getElems();
    assert multiset(c) == theMultiset;
    assert multiset(otherMapSeq) == other.theMultiset;
    equal? := multiset(c) == multiset(otherMapSeq);
    assert equal? <==> theMultiset == other.theMultiset;
    assert Valid();
  }

//gets the elements of the multiset as a sequence
  method getElems() returns (elems: seq<int>)
    requires Valid()
    ensures Valid()
    ensures multiset(elems) == theMultiset
  {
    var result : seq<int>;
    result := Map2Seq(elements);
    assert multiset(result) == theMultiset;
    elems := result;
    assert Valid();
  }

//Transforms a map to a sequence
  method Map2Seq(m: map<int, nat>) returns (s: seq<int>)
    requires forall i | i in m.Keys :: i in m.Keys <==> m[i] > 0
    ensures forall i | i in m.Keys :: multiset(s)[i] == m[i]
    ensures forall i | i in m.Keys :: i in s
    ensures A(m) == multiset(s)
    ensures (forall i | i in m :: m[i] == multiset(s)[i]) && (m == map[] <==> multiset(s) == multiset{})
  {
    if |m| == 0 { s := []; return; }

    var keys := m.Keys;
    var key: int;
    s := [];

    // Invariant: 
    // - For all i in m.Keys - keys, s contains exactly m[i] copies of i
    // - For all i in keys, s does not contain i
    // - |s| = sum of m[i] for i in m.Keys - keys
    // - keys subset of m.Keys
    // - keys union (m.Keys - keys) == m.Keys
    while keys != {}
      invariant keys <= m.Keys
      invariant forall i :: i in m.Keys - keys ==> multiset(s)[i] == m[i]
      invariant forall i :: i in keys ==> multiset(s)[i] == 0
      invariant |s| == (if m.Keys - keys == {} then 0 else sum i: m.Keys - keys :: m[i])
      decreases |keys|
    {

      key :| key in keys;

      var counter := 0;

      // Invariant: s already has multiset(s)[key] == counter, and for all i in m.Keys - keys, multiset(s)[i] == m[i]
      while counter < m[key]
        invariant 0 <= counter <= m[key]
        invariant multiset(s)[key] == counter
        invariant forall i :: i in m.Keys - keys ==> multiset(s)[i] == m[i]
        invariant forall i :: i in keys - {key} ==> multiset(s)[i] == 0
        decreases m[key] - counter
      {
        s := s + [key];
        counter := counter + 1;
      }

      keys := keys - {key};
    }
    assert forall i | i in m.Keys :: multiset(s)[i] == m[i];
    assert forall i | i in m.Keys :: i in s;
    LemmaReverseA(m, s);
    assert A(m) == multiset(s);
    assert (forall i | i in m :: m[i] == multiset(s)[i]) && (m == map[] <==> multiset(s) == multiset{});
  }

  // Helper function to produce a sequence from a map<int, nat>
  function SeqFromMap(m: map<int, nat>): seq<int>
    ensures multiset(SeqFromMap(m)) == (if m == map[] then multiset{} else multiset(SeqFromMap(m)))
    ensures forall i :: i in m ==> multiset(SeqFromMap(m))[i] == m[i]
    ensures (forall i :: i in m :: m[i] == multiset(SeqFromMap(m))[i]) && (m == map[] <==> multiset(SeqFromMap(m)) == multiset{})
  {
    if m == map[] then [] else
      var k :| k in m; SeqFromMap(m - {k}) + (if m[k] == 0 then [] else [k] * m[k])
  }

  method Test1()
    modifies this
  {

    assume this.theMultiset == multiset{1, 2, 3, 4};
    assume this.Valid();

    // get elements test
    var a := this.getElems();

    //declaring the other bag
    var theOtherBag : MultisetImplementationWithMap;
    theOtherBag := new MultisetImplementationWithMap.MultisetImplementationWithMap();

    // equals test - unequal bags
    var b:= this.equals(theOtherBag);

    // equals test - equal bags
    theOtherBag.theMultiset := multiset{1, 2, 3, 4};
    theOtherBag.elements := map[1 := 1, 2:=1, 3:=1,4:=1];
    var c:= this.equals(theOtherBag);
  }

  method Test2()
    modifies this
  {

    assume this.theMultiset == multiset{1, 2, 3, 4};
    assume this.Valid();

    // get elements test
    var a := this.getElems();

    //add test
    var d := this.Add(3);
    var e := this.getElems();

    //remove test
    var f := this.Remove(4);
    var g := this.getElems();

    //length test
    var h := this.Length();
  }

  method Test3()
  {

    //test Map2Seq
    var m := map[2:= 2, 3:=3, 4:= 4];
    var s :seq<int> := [2, 2, 3, 3, 3, 4, 4,4 ,4];

    var a := this.Map2Seq(m);

    var x := map[1 := 1, 2:= 1, 3:= 1];
    var y :seq<int> := [1, 2, 3];

    var z := this.Map2Seq(x);

  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
