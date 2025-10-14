module UtilitiesLibrary {
  function DropLast<T>(theSeq: seq<T>) : seq<T>
    requires 0 < |theSeq|
  {
    theSeq[..|theSeq|-1]
  }

  function Last<T>(theSeq: seq<T>) : T
    requires 0 < |theSeq|
  {
    theSeq[|theSeq|-1]
  }

  function UnionSeqOfSets<T>(theSets: seq<set<T>>) : set<T>
  {
    if |theSets| == 0 then {} else
      UnionSeqOfSets(DropLast(theSets)) + Last(theSets)
  }

  lemma SetsAreSubsetsOfUnion<T>(theSets: seq<set<T>>)
    ensures forall idx | 0<=idx<|theSets| :: theSets[idx] <= UnionSeqOfSets(theSets)
  {
    // Induction on |theSets|
    if |theSets| == 0 {
      // vacuously true
    } else {
      SetsAreSubsetsOfUnion(DropLast(theSets));
      // For all idx < |theSets|-1
      forall idx | 0 <= idx < |theSets|-1
        ensures theSets[idx] <= UnionSeqOfSets(theSets)
      {
        // By induction hypothesis
      }
      // For idx == |theSets|-1
      assert theSets[|theSets|-1] <= UnionSeqOfSets(theSets);
    }
  }

  lemma EachUnionMemberBelongsToASet<T>(theSets: seq<set<T>>)
    ensures forall member | member in UnionSeqOfSets(theSets) ::
          exists idx :: 0<=idx<|theSets| && member in theSets[idx]
  {
    if |theSets| == 0 {
      // vacuously true
    } else {
      EachUnionMemberBelongsToASet(DropLast(theSets));
      forall member | member in UnionSeqOfSets(theSets)
        ensures exists idx :: 0<=idx<|theSets| && member in theSets[idx]
      {
        if member in Last(theSets) {
          // member is in theSets[|theSets|-1]
          assert 0 <= |theSets|-1 < |theSets|;
          assert member in theSets[|theSets|-1];
        } else {
          // member must be in UnionSeqOfSets(DropLast(theSets))
          assert member in UnionSeqOfSets(DropLast(theSets));
          // By induction hypothesis
          var witness :| 0 <= witness < |theSets|-1 && member in theSets[witness];
          assert 0 <= witness < |theSets|-1 < |theSets|;
          assert member in theSets[witness];
        }
      }
    }
  }

  lemma GetIndexForMember<T>(theSets: seq<set<T>>, member: T) returns (idx:int)
    requires member in UnionSeqOfSets(theSets)
    ensures 0<=idx<|theSets|
    ensures member in theSets[idx]
  {
    EachUnionMemberBelongsToASet(theSets);
    var chosenIdx :| 0<=chosenIdx<|theSets| && member in theSets[chosenIdx];
    idx := chosenIdx;
  }

  datatype Option<T> = Some(value:T) | None

  function {:opaque} MapRemoveOne<K,V>(m:map<K,V>, key:K) : (m':map<K,V>)
    ensures forall k :: k in m && k != key ==> k in m'
    ensures forall k :: k in m' ==> k in m && k != key
    ensures forall j :: j in m' ==> m'[j] == m[j]
    ensures |m'.Keys| <= |m.Keys|
    ensures |m'| <= |m|
  {
    var m':= map j | j in m && j != key :: m[j];
    m'
  }

  ////////////// Library code for exercises 12 and 14 /////////////////////

  // This is tagged union, a "sum" datatype.
  datatype Direction = North() | East() | South() | West()

  function TurnRight(direction:Direction) : Direction
  {
    if direction.North?
      then East
    else if direction.East?
      then South
    else if direction.South?
      then West
    else  // By elimination, West!
      North
  }

  lemma Rotation()
    ensures TurnRight(TurnRight(TurnRight(TurnRight(North)))) == North
    ensures TurnRight(TurnRight(TurnRight(TurnRight(East)))) == East
    ensures TurnRight(TurnRight(TurnRight(TurnRight(South)))) == South
    ensures TurnRight(TurnRight(TurnRight(TurnRight(West)))) == West
    ensures TurnLeft(TurnLeft(TurnLeft(TurnLeft(North)))) == North
    ensures TurnLeft(TurnLeft(TurnLeft(TurnLeft(East)))) == East
    ensures TurnLeft(TurnLeft(TurnLeft(TurnLeft(South)))) == South
    ensures TurnLeft(TurnLeft(TurnLeft(TurnLeft(West)))) == West
    ensures TurnLeft(TurnRight(North)) == North
    ensures TurnRight(TurnLeft(North)) == North
    ensures TurnLeft(TurnRight(East)) == East
    ensures TurnRight(TurnLeft(East)) == East
    ensures TurnLeft(TurnRight(South)) == South
    ensures TurnRight(TurnLeft(South)) == South
    ensures TurnLeft(TurnRight(West)) == West
    ensures TurnRight(TurnLeft(West)) == West
  {
    // All ensures follow by case analysis
    assert TurnRight(TurnRight(TurnRight(TurnRight(North)))) == North;
    assert TurnRight(TurnRight(TurnRight(TurnRight(East)))) == East;
    assert TurnRight(TurnRight(TurnRight(TurnRight(South)))) == South;
    assert TurnRight(TurnRight(TurnRight(TurnRight(West)))) == West;
    assert TurnLeft(TurnLeft(TurnLeft(TurnLeft(North)))) == North;
    assert TurnLeft(TurnLeft(TurnLeft(TurnLeft(East)))) == East;
    assert TurnLeft(TurnLeft(TurnLeft(TurnLeft(South)))) == South;
    assert TurnLeft(TurnLeft(TurnLeft(TurnLeft(West)))) == West;
    assert TurnLeft(TurnRight(North)) == North;
    assert TurnRight(TurnLeft(North)) == North;
    assert TurnLeft(TurnRight(East)) == East;
    assert TurnRight(TurnLeft(East)) == East;
    assert TurnLeft(TurnRight(South)) == South;
    assert TurnRight(TurnLeft(South)) == South;
    assert TurnLeft(TurnRight(West)) == West;
    assert TurnRight(TurnLeft(West)) == West;
  }

  function TurnLeft(direction:Direction) : Direction
  {
    match direction {
      case North => West
      case West => South
      case South => East
      case East => North
    }
  }

  ////////////// Library code for exercises 13 and 14 /////////////////////

  datatype Meat = Salami | Ham
  datatype Cheese = Provolone | Swiss | Cheddar | Jack
  datatype Veggie = Olive | Onion | Pepper
  datatype Order =
      Sandwich(meat:Meat, cheese:Cheese)
    | Pizza(meat:Meat, veggie:Veggie)
    | Appetizer(cheese:Cheese)

  // There are 2 Meats, 4 Cheeses, and 3 Veggies.
  // Thus there are 8 Sandwiches, 6 Pizzas, and 4 Appetizers.
  // Thus there are 8+6+4 = 18 Orders.
  // This is why they're called "algebraic" datatypes.

}
function abs(a: real) : real {if a>0.0 then a else -a}
