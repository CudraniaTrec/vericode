
module SetBijectivity {
  lemma BijectivityImpliesEqualCardinality<A, B>(setA: set<A>, setB: set<B>, relation: iset<(A, B)>)
    requires forall a :: a in setA ==> exists b :: b in setB && (a, b) in relation
    requires forall a1, a2, b :: a1 in setA && a2 in setA && b in setB && (a1, b) in relation && (a2, b) in relation ==> a1 == a2
    requires forall b :: b in setB ==> exists a :: a in setA && (a, b) in relation
    requires forall a, b1, b2 :: b1 in setB && b2 in setB && a in setA && (a, b1) in relation && (a, b2) in relation ==> b1 == b2
    ensures |setA| == |setB|
  {
    if |setA| == 0 {
      assert setB == {};
      assert |setB| == 0;
    } else {
      var a :| a in setA;
      var b :| b in setB && (a, b) in relation;
      var setA' := setA - {a};
      var setB' := setB - {b};
      // Strongest possible assertions and invariants
      assert a in setA;
      assert b in setB;
      assert (a, b) in relation;
      assert forall a1 :: a1 in setA' ==> exists b1 :: b1 in setB' && (a1, b1) in relation;
      assert forall a1, a2, b1 :: a1 in setA' && a2 in setA' && b1 in setB' && (a1, b1) in relation && (a2, b1) in relation ==> a1 == a2;
      assert forall b1 :: b1 in setB' ==> exists a1 :: a1 in setA' && (a1, b1) in relation;
      assert forall a1, b1, b2 :: b1 in setB' && b2 in setB' && a1 in setA' && (a1, b1) in relation && (a1, b2) in relation ==> b1 == b2;
      BijectivityImpliesEqualCardinality(setA', setB', relation);
      assert |setA| == |setA'| + 1;
      assert |setB| == |setB'| + 1;
      assert |setA'| == |setB'|;
      assert |setA| == |setB|;
    }
  }

  lemma CrossProductCardinality<A, B>(setA: set<A>, setB: set<B>, cp: set<(A,B)>)
  requires cp == (set a, b | a in setA && b in setB :: (a,b))
  ensures |cp| == |setA| * |setB|;
  {
    if |setA| == 0 {
      assert cp == {};
      assert |cp| == 0;
      assert |setA| * |setB| == 0;
    } else {
      var x :| x in setA;
      var setA' := setA - {x};
      var cp' := (set a, b | a in setA' && b in setB :: (a,b));
      var line := (set a, b | a == x && b in setB :: (a,b));
      assert cp == cp' + line;
      assert cp' ** line == {};
      assert |cp| == |cp'| + |line|;
      assert |line| == |setB|;
      var relation := iset p : ((A, B), B) | p.0.1 == p.1;
      forall b | b in setB
        ensures exists p :: p in line && (p, b) in relation
      {
        var p := (x, b);
        assert p in line;
        assert (p, b) in relation;
      }
      assert forall p1, p2, b :: p1 in line && p2 in line && b in setB && (p1, b) in relation && (p2, b) in relation ==> p1 == p2;
      assert forall b :: b in setB ==> exists p :: p in line && (p, b) in relation;
      assert forall p :: p in line ==> exists b :: b in setB && (p, b) in relation;
      assert forall p, b1, b2 :: b1 in setB && b2 in setB && p in line && (p, b1) in relation && (p, b2) in relation ==> b1 == b2;
      BijectivityImpliesEqualCardinality(line, setB, relation);
      CrossProductCardinality(setA', setB, cp');
      assert |cp'| == |setA'| * |setB|;
      assert |cp| == |cp'| + |line|;
      assert |cp| == (|setA| - 1) * |setB| + |setB|;
      assert |cp| == |setA| * |setB|;
    }
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
