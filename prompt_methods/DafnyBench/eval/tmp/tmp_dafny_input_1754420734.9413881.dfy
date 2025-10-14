module Sets {

  lemma {:opaque} ProperSubsetImpliesSmallerCardinality<T>(a: set<T>, b: set<T>)
    requires a < b
    ensures |a| < |b|
  {
    // a < b means a ⊆ b and a ≠ b
    // By SetInclusionImpliesSmallerCardinality, |a| ≤ |b|
    // If |a| == |b|, then a == b by SetInclusionAndEqualCardinalityImpliesSetEquality, contradiction
    SetInclusionImpliesSmallerCardinality(a, b);
    if |a| == |b| {
      SetInclusionAndEqualCardinalityImpliesSetEquality(a, b);
      assert false;
    }
    assert |a| < |b|;
  }

  lemma {:opaque} SetInclusionImpliesSmallerCardinality<T>(a: set<T>, b: set<T>)
    requires a <= b
    ensures |a| <= |b|
  {
    // The cardinality of a subset is at most the cardinality of the superset
    // This is a standard property of sets
    // Proof by induction on |a|
    if a == {} {
      assert |a| == 0;
      assert 0 <= |b|;
    } else {
      var x :| x in a;
      var a' := a - {x};
      assert a' <= b;
      SetInclusionImpliesSmallerCardinality(a', b);
      assert |a| == |a'| + 1;
      assert |a'| <= |b|;
      assert |a| <= |b|;
    }
  }

  lemma {:opaque} SetInclusionImpliesStrictlySmallerCardinality<T>(a: set<T>, b: set<T>)
    requires a < b
    ensures |a| < |b|
  {
    ProperSubsetImpliesSmallerCardinality(a, b);
    assert |a| < |b|;
  }

  lemma {:opaque} SetInclusionAndEqualCardinalityImpliesSetEquality<T>(a: set<T>, b: set<T>)
    requires a <= b
    requires |a| == |b|
    ensures a == b
  {
    // If a ⊆ b and |a| == |b|, then a == b
    // Suppose for contradiction there exists x in b but not in a
    // Then |a| < |b|, contradiction
    assert a <= b;
    assert |a| == |b|;
    assert a == b;
  }

  function SetRange(n: int) : set<int>
  {
    set i | 0 <= i < n
  }

  lemma CardinalitySetRange(n: int)
  requires n >= 0
  ensures |SetRange(n)| == n
  {
    if n == 0 {
      assert SetRange(0) == {};
      assert |SetRange(0)| == 0;
    } else {
      CardinalitySetRange(n-1);
      assert SetRange(n) == SetRange(n-1) + {n-1};
      assert n-1 !in SetRange(n-1);
      assert |SetRange(n)| == |SetRange(n-1)| + 1;
      assert |SetRange(n-1)| == n-1;
      assert |SetRange(n)| == n;
    }
  }
}
function abs(a: real) : real {if a>0.0 then a else -a}
