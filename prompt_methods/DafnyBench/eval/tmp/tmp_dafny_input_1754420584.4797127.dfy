
/*
  Class CircularArray.

  Names:
  Arthur Sudbrack Ibarra,
  Miguel Torres de Castro,
  Felipe Grosze Nipper,
  Willian Magnum Albeche,
  Luiz Eduardo Mello dos Reis.
*/
class {:autocontracts} CircularArray {
  /*
    Implementation
  */
  var arr: array<int>; // The array.
  var start: nat; // The index of the first element.
  var size: nat; // The number of elements in the queue.

  /*
    Abstraction.
  */
  ghost const Capacity: nat; // The capacity of the queue. (WE WERE UNABLE TO MAKE THE SIZE OF THE ARRAY DYNAMIC).
  ghost var Elements: seq<int>; // The elements in the array represented as a sequence.

  /*
    Class invariant.
  */
  ghost predicate Valid()
  {
    0 <= start < arr.Length &&
    0 <= size <= arr.Length &&
    Capacity == arr.Length &&
    Elements == if start + size <= arr.Length
                then arr[start..start + size]
                else arr[start..] + arr[..size - (arr.Length - start)]
  }

  /*
    Constructor.
  */
  constructor EmptyQueue(capacity: nat)
    requires capacity > 0
    ensures Elements == []
    ensures Capacity == capacity
  {
    arr := new int[capacity];
    start := 0;
    size := 0;
    Capacity := capacity;
    Elements := [];
    assert Valid();
  }

  /*
    Enqueue Method
  */
  method Enqueue(e: int)
    requires !IsFull()
    ensures Elements == old(Elements) + [e]
  {
    assert Valid();
    var idx := (start + size) % arr.Length;
    arr[idx] := e;
    size := size + 1;
    Elements := Elements + [e];
    assert Valid();
    assert Elements == old(Elements) + [e];
  }

  /*
    Dequeue method.
  */
  method Dequeue() returns (e: int)
    requires !IsEmpty()
    ensures Elements == old(Elements)[1..]
    ensures e == old(Elements)[0]
  {
    assert Valid();
    e := arr[start];
    if start + 1 < arr.Length {
      start := start + 1;
    }
    else {
      start := 0;
    }
    size := size - 1;
    Elements := Elements[1..];
    assert Valid();
    assert Elements == old(Elements)[1..];
    assert e == old(Elements)[0];
  }

  /*
    Contains predicate.
  */
  predicate Contains(e: int)
    ensures Contains(e) == (e in Elements)
  {
    if start + size < arr.Length then
      e in arr[start..start + size]
    else
      e in arr[start..] + arr[..size - (arr.Length - start)]
  }

  /*
    Size function.
  */
  function Size(): nat
    ensures Size() == |Elements|
  {
    size
  }

  /*
    IsEmpty predicate.
  */
  predicate IsEmpty()
    ensures IsEmpty() <==> (|Elements| == 0)
  {
    size == 0
  }

  /*
    IsFull predicate.
  */
  predicate IsFull()
    ensures IsFull() <==> |Elements| == Capacity
  {
    size == arr.Length
  }

  /*
    GetAt method.
    (Not requested in the assignment, but useful).
  */
  method GetAt(i: nat) returns (e: int)
    requires i < size
    ensures e == Elements[i]
  {
    assert Valid();
    var idx := (start + i) % arr.Length;
    e := arr[idx];
    if start + size <= arr.Length {
      assert Elements == arr[start..start + size];
      assert e == arr[start + i];
      assert e == Elements[i];
    } else {
      var cut := arr[start..] + arr[..size - (arr.Length - start)];
      assert Elements == cut;
      assert e == cut[i];
      assert e == Elements[i];
    }
  }

  /*
    AsSequence method.
    (Auxiliary method for the Concatenate method)
  */
  method AsSequence() returns (s: seq<int>)
    ensures s == Elements
  {
    if start + size <= arr.Length {
      s := arr[start..start + size];
      assert s == Elements;
    } else {
      s := arr[start..] + arr[..size - (arr.Length - start)];
      assert s == Elements;
    }
  }

  /*
    Concatenate method.
  */
  method Concatenate(q1: CircularArray) returns(q2: CircularArray)
    requires q1.Valid()
    requires q1 != this
    ensures fresh(q2)
    ensures q2.Capacity == Capacity + q1.Capacity
    ensures q2.Elements == Elements + q1.Elements
  {
    q2 := new CircularArray.EmptyQueue(arr.Length + q1.arr.Length);
    var s1 := AsSequence();
    var s2 := q1.AsSequence();
    var both := s1 + s2;
    // Copy this queue's elements
    var i: nat := 0;
    while i < size
      invariant 0 <= i <= size
      invariant forall j :: 0 <= j < i ==> q2.arr[j] == both[j]
    {
      q2.arr[i] := both[i];
      i := i + 1;
    }
    // Copy q1's elements
    var j: nat := 0;
    while j < q1.size
      invariant 0 <= j <= q1.size
      invariant forall k :: 0 <= k < j ==> q2.arr[size + k] == both[size + k]
    {
      q2.arr[size + j] := both[size + j];
      j := j + 1;
    }
    q2.size := size + q1.size;
    q2.start := 0;
    q2.Elements := Elements + q1.Elements;
    assert q2.Capacity == Capacity + q1.Capacity;
    assert q2.Elements == Elements + q1.Elements;
    assert q2.Valid();
    print q2.arr.Length;
    print q2.size;
  }
}

/*
  Main method.
  Here the the CircularArray class is demonstrated.
*/
method Main()
{
  var q := new CircularArray.EmptyQueue(10); // Create a new queue.

  q.Enqueue(1); // Enqueue the element 1.
  var e1 := q.GetAt(0); // Get the element at index 0.

  q.Enqueue(2); // Enqueue the element 2.
  var e2 := q.GetAt(1); // Get the element at index 1.

  var e := q.Dequeue(); // Dequeue the element 1.

  q.Enqueue(3); // Enqueue the element 3.

  e := q.Dequeue(); // Dequeue the element 2.

  e := q.Dequeue(); // Dequeue the element 3.

}

function abs(a: real) : real {if a>0.0 then a else -a}
