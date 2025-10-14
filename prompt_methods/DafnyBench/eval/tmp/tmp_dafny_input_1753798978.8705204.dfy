/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

// RUN: %verify "%s"
   
/**
  *  Implements mutable maps in Dafny to guard against inconsistent specifications.
  *  Only exists to verify feasability; not meant for actual usage.
  */
module {:options "-functionSyntax:4"} MutableMapDafny {
  /**
    *  NOTE: Only here because of #2500; once resolved import "MutableMapTrait.dfy".
    */
  trait {:termination false} MutableMapTrait<K(==),V(==)> {
    function content(): map<K, V>
      reads this

    method Put(k: K, v: V)
      modifies this
      ensures this.content() == old(this.content())[k := v]   
      ensures k in old(this.content()).Keys ==> this.content().Values + {old(this.content())[k]} == old(this.content()).Values + {v}
      ensures k !in old(this.content()).Keys ==> this.content().Values == old(this.content()).Values + {v}

    function Keys(): (keys: set<K>)
      reads this
      ensures keys == this.content().Keys

    predicate HasKey(k: K)
      reads this
      ensures HasKey(k) <==> k in this.content().Keys

    function Values(): (values: set<V>)
      reads this
      ensures values == this.content().Values

    function Items(): (items: set<(K,V)>)
      reads this
      ensures items == this.content().Items
      ensures items == set k | k in this.content().Keys :: (k, this.content()[k])

    function Select(k: K): (v: V)
      reads this
      requires this.HasKey(k)
      ensures v in this.content().Values
      ensures this.content()[k] == v

    method Remove(k: K)
      modifies this
      ensures this.content() == old(this.content()) - {k}
      ensures k in old(this.content()).Keys ==> this.content().Values + {old(this.content())[k]} == old(this.content()).Values
 
    function Size(): (size: int)
      reads this
      ensures size == |this.content().Items|
  }

  class MutableMapDafny<K(==),V(==)> extends MutableMapTrait<K,V> {
    var m: map<K,V>

    function content(): map<K, V> 
      reads this
    {
      m
    }

    constructor ()
      ensures this.content() == map[]
    {
      m := map[];
      assert m == map[];
    }

    method Put(k: K, v: V)
      modifies this
      ensures this.content() == old(this.content())[k := v]   
      ensures k in old(this.content()).Keys ==> this.content().Values + {old(this.content())[k]} == old(this.content()).Values + {v}
      ensures k !in old(this.content()).Keys ==> this.content().Values == old(this.content()).Values + {v}
    {
      var oldM := m;
      m := m[k := v];
      assert m == oldM[k := v];
      if k in oldM.Keys {
        assert oldM[k] in oldM.Values;
        assert m.Values + {oldM[k]} == oldM.Values + {v};
        forall v' | v' in oldM.Values + {v} 
          ensures v' in m.Values + {oldM[k]} 
        {
          if v' == v {
            assert v' in m.Values;
          } else if v' == oldM[k] {
            assert v' in oldM.Values;
          } else {
            assert v' in oldM.Values;
            assert v' in m.Values;
          }
        }
      }
      if k !in oldM.Keys {
        assert m.Values == oldM.Values + {v};
        forall v' | v' in oldM.Values + {v} 
          ensures v' in m.Values 
        {
          if v' == v {
            assert v' in m.Values;
          } else {
            assert v' in oldM.Values;
            assert v' in m.Values;
          }
        }
      }
      assert m == old(m)[k := v];
    }

    function Keys(): (keys: set<K>)
      reads this
      ensures keys == this.content().Keys
    {
      assert m.Keys == content().Keys;
      m.Keys
    }

    predicate HasKey(k: K)
      reads this
      ensures HasKey(k) <==> k in this.content().Keys
    {
      assert (k in m.Keys) <==> (k in content().Keys);
      k in m.Keys
    }

    function Values(): (values: set<V>)
      reads this
      ensures values == this.content().Values
    {
      assert m.Values == content().Values;
      m.Values
    }

    function Items(): (items: set<(K,V)>)
      reads this
      ensures items == this.content().Items
      ensures items == set k | k in this.content().Keys :: (k, this.content()[k])
    {
      var items := set k | k in m.Keys :: (k, m[k]);
      assert items == m.Items;
      assert items == set k | k in content().Keys :: (k, content()[k]);
      forall k | k in m.Keys ensures (k, m[k]) in m.Items {
        assert (k, m[k]) in m.Items;
      }
      forall x | x in m.Items ensures x in items {
        assert x in items;
      }
      items
    }

    function Select(k: K): (v: V)
      reads this
      requires this.HasKey(k)
      ensures v in this.content().Values
      ensures this.content()[k] == v
    {
      assert k in m.Keys;
      assert m[k] in m.Values;
      assert content()[k] == m[k];
      m[k]
    }

    method Remove(k: K)
      modifies this
      ensures this.content() == old(this.content()) - {k}
      ensures k in old(this.content()).Keys ==> this.content().Values + {old(this.content())[k]} == old(this.content()).Values
    {
      var oldM := m;
      m := map k' | k' in m.Keys && k' != k :: m[k'];
      assert m == old(oldM) - {k};
      if k in oldM.Keys {
        var v := oldM[k];
        assert v in oldM.Values;
        assert m.Values + {v} == oldM.Values;
        forall v' | v' in oldM.Values ensures v' in m.Values + {v} {
          if v' == v {
            assert v' !in m.Values;
          } else {
            assert v' in m.Values;
          }
        }
      }
      assert m == old(m) - {k};
    }

    function Size(): (size: int)
      reads this
      ensures size == |this.content().Items|
    {
      assert |m| == |content().Items|;
      |m|
    }
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
