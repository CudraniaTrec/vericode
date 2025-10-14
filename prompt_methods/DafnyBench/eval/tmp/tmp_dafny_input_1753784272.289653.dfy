class LFUCache {

    var capacity : int;
    var cacheMap : map<int, (int, int)>; //key -> {value, freq}

    constructor(capacity: int)
      requires capacity > 0;
      ensures Valid();
    {
      this.capacity := capacity;
      this.cacheMap := map[];
    }

    predicate Valid()
      reads this;
    {
      this.capacity > 0 &&
      0 <= |cacheMap| <= capacity &&
      (|cacheMap| > 0 ==> (forall k :: k in cacheMap ==> cacheMap[k].1 >= 1)) &&
      (|cacheMap| > 0 ==> (forall k :: k in cacheMap ==> cacheMap[k].0 >= 0))
    } 

    method getLFUKey() returns (lfuKey : int) 
      requires Valid();
      requires |cacheMap| > 0;
      ensures Valid();
      ensures lfuKey in cacheMap;
      ensures forall k :: k in cacheMap ==> cacheMap[lfuKey].1 <= cacheMap[k].1;
    {
      var keys := cacheMap.Keys;
      var seenKeys: set<int> := {};

      var anyKey :| anyKey in keys;
      var minFreq := cacheMap[anyKey].1;
      lfuKey := anyKey;

      while keys != {}
        invariant keys + seenKeys == cacheMap.Keys
        invariant seenKeys <= cacheMap.Keys
        invariant lfuKey in seenKeys + keys
        invariant |keys| + |seenKeys| == |cacheMap|
        invariant forall k :: k in seenKeys ==> cacheMap[lfuKey].1 <= cacheMap[k].1
        decreases |keys|
      {
        var k :| k in keys;
        if (cacheMap[k].1 < minFreq) {
          lfuKey := k;
          minFreq := cacheMap[k].1;
        }
        keys := keys - { k };
        seenKeys := seenKeys + { k };
      }
      assert forall k :: k in cacheMap ==> cacheMap[lfuKey].1 <= cacheMap[k].1;
      return lfuKey;
    }

    method get(key: int) returns (value: int)
      requires Valid();
      modifies this;
      ensures Valid();
      ensures key !in cacheMap ==> value == -1;
      ensures forall e :: e in old(cacheMap) <==> e in cacheMap;
      ensures forall e :: e in old(cacheMap) ==> (old(cacheMap[e].0) == cacheMap[e].0);
      ensures key in cacheMap ==> value == cacheMap[key].0 && old(cacheMap[key].1) == cacheMap[key].1-1;
    {
      if(key !in cacheMap) {
        value := -1;
      }
      else{
        value := cacheMap[key].0;
        var oldFreq := cacheMap[key].1;
        var newV := (value, oldFreq + 1);
        cacheMap := cacheMap[key := newV];
        assert cacheMap[key].1 == oldFreq + 1;
        assert cacheMap[key].0 == value;
        assert forall e :: e != key && e in old(cacheMap) ==> cacheMap[e] == old(cacheMap)[e];
      }
      print "after get: ";
      print cacheMap;
      print "\n";
      return value;
    }
    
    
     method put(key: int, value: int)
        requires Valid();
        requires value > 0;
        modifies this
        ensures Valid();
       
     {
        if (key in cacheMap) {
          var currFreq := cacheMap[key].1;
          cacheMap := cacheMap[key := (value, currFreq)];
          assert cacheMap[key] == (value, currFreq);
          assert forall e :: e != key && e in old(cacheMap) ==> cacheMap[e] == old(cacheMap)[e];
        } else {
          if (|cacheMap| < capacity) {
            cacheMap := cacheMap[key := (value, 1)];
            assert |cacheMap| <= capacity;
            assert cacheMap[key] == (value, 1);
          } else {
            var LFUKey := getLFUKey();
            ghost var oldMap := cacheMap;
            var newMap := cacheMap - {LFUKey};
            assert LFUKey in cacheMap;
            assert |newMap| == |cacheMap| - 1;
            cacheMap := newMap;
            ghost var oldCard := |oldMap|;
            ghost var newCard := |newMap|;
            assert oldCard == newCard + 1;
            cacheMap := cacheMap[key := (value, 1)];
            assert |cacheMap| == oldCard;
            assert cacheMap[key] == (value, 1);
          }
        }
        assert Valid();
        print "after put: ";
        print cacheMap;
        print "\n";
     }
 }

 method Main()
 {
   var LFUCache := new LFUCache(5);
   print "Cache Capacity = 5 \n";
   print "PUT (1, 1) - ";
   LFUCache.put(1,1);
   print "PUT (2, 2) - ";
   LFUCache.put(2,2);
   print "PUT (3, 3) - ";
   LFUCache.put(3,3);
   print "GET (1) - ";
   var val := LFUCache.get(1);
   print "get(1) = ";
   print val;
   print "\n";
   print "PUT (3, 5) - ";
   LFUCache.put(3,5);
   print "GET (3) - ";
   val := LFUCache.get(3);
   print "get(3) = ";
   print val;
   print "\n";
   print "PUT (4, 6) - ";
   LFUCache.put(4,6);
   print "PUT (5, 7) - ";
   LFUCache.put(5,7);
   print "PUT (10, 100) - ";
   LFUCache.put(10,100);
   print "GET (2) - ";
   val := LFUCache.get(2);
   print "get(2) = ";
   print val;
   print "\n";
 }

function abs(a: real) : real {if a>0.0 then a else -a}
