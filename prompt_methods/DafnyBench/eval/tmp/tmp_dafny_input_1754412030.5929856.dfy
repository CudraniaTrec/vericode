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
    }

    method Put(k: K, v: V)
      modifies this
      ensures this.content() == old(this.content())[k := v]   
      ensures k in old(this.content()).Keys ==> this.content().Values + {old(this.content())[k]} == old(this.content()).Values + {v}
      ensures k !in old(this.content()).Keys ==> this.content().Values == old(this.content()).Values + {v}
    {
      var oldM := m;
      m := m[k := v];
      // No assertion here: let postconditions do the work
      // Strongest possible: prove the value set properties
      if k in oldM.Keys {
        // m.Values + {oldM[k]} == oldM.Values + {v}
        // Forall annotation for the postcondition
        assert m.Keys == oldM.Keys;
        assert m[k] == v;
        assert oldM[k] in oldM.Values;
        assert v in m.Values;
        // For all x: x in oldM.Values + {v} <==> x in m.Values + {oldM[k]}
        // This is implied by the postcondition and map update semantics
      } else {
        // m.Values == oldM.Values + {v}
        assert m.Keys == oldM.Keys + {k};
        assert m[k] == v;
        assert v in m.Values;
        // For all x: x in oldM.Values + {v} <==> x in m.Values
      }
    }

    function Keys(): (keys: set<K>)
      reads this
      ensures keys == this.content().Keys
    {
      m.Keys
    }

    predicate HasKey(k: K)
      reads this
      ensures HasKey(k) <==> k in this.content().Keys
    {
      k in m.Keys
    }

    function Values(): (values: set<V>)
      reads this
      ensures values == this.content().Values
    {
      m.Values
    }

    function Items(): (items: set<(K,V)>)
      reads this
      ensures items == this.content().Items
      ensures items == set k | k in this.content().Keys :: (k, this.content()[k])
    {
      set k | k in m.Keys :: (k, m[k])
    }

    function Select(k: K): (v: V)
      reads this
      requires this.HasKey(k)
      ensures v in this.content().Values
      ensures this.content()[k] == v
    {
      m[k]
    }

    method Remove(k: K)
      modifies this
      ensures this.content() == old(this.content()) - {k}
      ensures k in old(this.content()).Keys ==> this.content().Values + {old(this.content())[k]} == old(this.content()).Values
    {
      var oldM := m;
      m := map k' | k' in m.Keys && k' != k :: m[k'];
      // Strongest possible: prove the value set property for the postcondition
      if k in oldM.Keys {
        var v := oldM[k];
        // m.Values + {v} == oldM.Values
        // For all x: x in oldM.Values ==> x in m.Values or x == v
        // For all x: x in m.Values ==> x in oldM.Values and x != v
      }
    }

    function Size(): (size: int)
      reads this
      ensures size == |this.content().Items|
    {
      |m|
    }
  }
}
function abs(a: real) : real {if a>0.0 then a else -a}
