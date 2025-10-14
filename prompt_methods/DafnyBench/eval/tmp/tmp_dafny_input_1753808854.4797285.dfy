module Sets {

  lemma {:opaque} ProperSubsetImpliesSmallerCardinality<T>(a: set<T>, b: set<T>)
    requires a < b
    ensures |a| < |b|
  {
    // a < b means a ⊆ b and a ≠ b, so there is at least one element in b not in a
    assert a <= b;
    assert a != b;
    var x :| x in b && x !in a;
    assert x !in a;
    assert x in b;
    assert |a + {x}| == |a| + 1;
    assert a + {x} <= b;
    assert |a + {x}| <= |b|;
    assert |a| + 1 <= |b|;
    assert |a| < |b|;
  }

  lemma {:opaque} SetInclusionImpliesSmallerCardinality<T>(a: set<T>, b: set<T>)
    requires a <= b
    ensures |a| <= |b|
  {
    if a == b {
      assert |a| == |b|;
    } else {
      assert a < b;
      ProperSubsetImpliesSmallerCardinality(a, b);
      assert |a| < |b|;
      assert |a| <= |b|;
    }
  }

  lemma {:opaque} SetInclusionImpliesStrictlySmallerCardinality<T>(a: set<T>, b: set<T>)
    requires a < b
    ensures |a| < |b|
  {
    ProperSubsetImpliesSmallerCardinality(a, b);
  }

  lemma {:opaque} SetInclusionAndEqualCardinalityImpliesSetEquality<T>(a: set<T>, b: set<T>)
    requires a <= b
    requires |a| == |b|
    ensures a == b
  {
    if a == b {
      assert true;
    } else {
      assert a < b;
      ProperSubsetImpliesSmallerCardinality(a, b);
      assert |a| < |b|;
      assert false; // Contradicts |a| == |b|
    }
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
