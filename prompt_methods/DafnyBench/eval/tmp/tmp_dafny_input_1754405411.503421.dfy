
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
    (forall i | i in elements.Keys :: elements[i] > 0)
    && (theMultiset == A(elements))
    && (forall i :: i in elements.Keys <==> Contains(i))
  }

  // the abstraction function
  function A(m: map<int, nat>): multiset<int>
    ensures (forall i | i in m :: m[i] == A(m)[i])
    ensures (m == map[] <==> A(m) == multiset{})
    ensures (forall i :: i in m <==> i in A(m))
  {
    if |m| == 0 then multiset{} else
      var k :| k in m.Keys;
      multiset([k]) * m[k] + A(m - {k})
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
    } else {
      elements := elements[elem := elements[elem] + 1];
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
      assert elements == old(elements);
      assert Valid();
      return;
    }
    var oldCount := elements[elem];
    elements := elements[elem := elements[elem] - 1];
    if elements[elem] == 0 {
      elements := elements - {elem};
    }
    theMultiset := A(elements);
    didChange := true;
    assert theMultiset == old(theMultiset) - multiset{elem};
    assert Valid();
    assert elements != old(elements);
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
    assert multiset(elems) == theMultiset;
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
    s := [];
    var keys := m.Keys;
    while keys != {}
      invariant keys <= m.Keys
      invariant (forall i :: i in m.Keys - keys ==> multiset(s)[i] == m[i])
      invariant (forall i :: i in keys ==> multiset(s)[i] == 0)
      invariant (forall i :: i in m.Keys :: multiset(s)[i] + (if i in keys then 0 else m[i]) == m[i])
      invariant (|s| == (sum i | i in m.Keys - keys :: m[i]))
      decreases |keys|
    {
      var key :| key in keys;
      var counter := 0;
      while counter < m[key]
        invariant 0 <= counter <= m[key]
        invariant multiset(s)[key] == counter
        invariant (forall i :: i in m.Keys - keys ==> multiset(s)[i] == m[i])
        invariant (forall i :: i in keys - {key} ==> multiset(s)[i] == 0)
        decreases m[key] - counter
      {
        s := s + [key];
        counter := counter + 1;
      }
      keys := keys - {key};
    }
    assert (forall i | i in m.Keys :: multiset(s)[i] == m[i]);
    assert (forall i :: i in m.Keys :: i in s);
    LemmaReverseA(m, s);
    assert A(m) == multiset(s);
    assert (forall i | i in m :: m[i] == multiset(s)[i]) && (m == map[] <==> multiset(s) == multiset{});
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
