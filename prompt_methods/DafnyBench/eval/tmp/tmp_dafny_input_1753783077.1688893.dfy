
class {:autocontracts} Queue {

  var circularQueue: array<int>;
  var rear: nat;  // cauda
  var front: nat; // head
  var counter: nat;

  ghost var Content: seq<int>;

  ghost predicate Valid()
  {
    0 <= counter <= circularQueue.Length &&
    0 <= front <= circularQueue.Length &&
    0 <= rear <= circularQueue.Length &&
    |Content| == counter &&
    circularQueue.Length == |Content| &&
    (forall i :: 0 <= i < circularQueue.Length ==> circularQueue[i] == Content[i])
  }

  constructor()
    ensures circularQueue.Length == 0
    ensures front == 0 && rear == 0
    ensures Content == []
    ensures counter == 0
  {
    circularQueue := new int[0];
    rear := 0;
    front := 0;
    Content := [];
    counter := 0;
  }

  method insert(item: int)
  {
    if front == 0 && rear == 0 && circularQueue.Length == 0
    {
      auxInsertEmptyQueue(item);
    }
    else if front == 0 && rear == circularQueue.Length && circularQueue.Length >= 1
    {
      auxInsertEndQueue(item);
    }
    else if rear < front && front < circularQueue.Length
    {
      auxInsertSpaceQueue(item);
    }
    else if rear + 1 == front && circularQueue.Length > 0
    {
      auxInsertBetweenQueue(item);
    }
  }

  method auxInsertEmptyQueue(item:int)
    requires front == 0 && rear == 0 && circularQueue.Length == 0
    ensures circularQueue.Length == 1
    ensures Content == [item]
    ensures |Content| == 1
    ensures rear == 1
    ensures counter == old(counter) + 1
    ensures front == 0
  {
    counter := counter + 1;
    var queueInsert: array<int>;
    queueInsert := new int [1];
    queueInsert[0] := item;
    circularQueue := queueInsert;
    Content := [item];
    rear := 1;
  }

  method auxInsertEndQueue(item:int)
    requires front == 0 && rear == circularQueue.Length && circularQueue.Length >= 1
    ensures Content == old(Content) + [item]
    ensures |Content| == old(|Content|) + 1
    ensures front == 0
    ensures rear == old(rear) + 1
    ensures counter == old(counter) + 1
  {
    counter := counter + 1;
    var queueInsert: array<int>;
    queueInsert := new int [circularQueue.Length + 1];
    var i: nat := 0;
    while i < circularQueue.Length
      invariant 0 <= i <= circularQueue.Length
      invariant queueInsert.Length == circularQueue.Length + 1
      invariant forall j :: 0 <= j < i ==> queueInsert[j] == circularQueue[j]
    {
      queueInsert[i] := circularQueue[i];
      i := i + 1;
    }
    queueInsert[queueInsert.Length - 1] := item;
    circularQueue := queueInsert;
    Content := Content + [item];
    rear := rear + 1;
    front := 0;
  }

  method auxInsertSpaceQueue(item:int)
    requires rear < front && front < circularQueue.Length
    ensures rear == old(rear) + 1
    ensures counter == old(counter) + 1
    ensures Content == old(Content[0..old(rear)]) + [item] + old(Content[old(rear)..circularQueue.Length-1])
    ensures |Content| == old(|Content|) + 1
  {
    var oldRear := rear;
    counter := counter + 1;
    var queueInsert: array<int>;
    queueInsert := new int [circularQueue.Length + 1];
    var i: nat := 0;
    while i < oldRear
      invariant 0 <= i <= oldRear
      invariant queueInsert.Length == circularQueue.Length + 1
      invariant forall j :: 0 <= j < i ==> queueInsert[j] == circularQueue[j]
    {
      queueInsert[i] := circularQueue[i];
      i := i + 1;
    }
    queueInsert[oldRear] := item;
    i := oldRear;
    while i < circularQueue.Length
      invariant oldRear <= i <= circularQueue.Length
      invariant forall j :: oldRear < j <= i ==> queueInsert[j] == circularQueue[j-1]
    {
      queueInsert[i+1] := circularQueue[i];
      i := i + 1;
    }
    circularQueue := queueInsert;
    Content := Content[0..oldRear] + [item] + Content[oldRear..circularQueue.Length-1];
    rear := oldRear + 1;
  }

  method auxInsertInitQueue(item:int)
  {
    // Not implemented
  }

  method auxInsertBetweenQueue(item:int)
  {
    // Not implemented
  }

  method remove() returns (item: int)
    requires front < circularQueue.Length
    requires circularQueue.Length > 0
    ensures rear <= |old(Content)|
    ensures circularQueue.Length > 0
    ensures item == old(Content)[old(front)]
    ensures front == (old(front) + 1) % circularQueue.Length
    ensures old(front) < rear ==> Content == old(Content)[old(front)+1..rear]
    ensures old(front) > rear ==> Content == old(Content)[0 .. rear] + old(Content)[old(front)+1..|old(Content)|]
  {
    var oldFront := front;
    item := circularQueue[front];
    front := (front + 1) % circularQueue.Length;
    counter := counter - 1;
    if oldFront < rear {
      Content := Content[oldFront+1..rear];
    } else if oldFront > rear {
      Content := Content[0..rear] + Content[oldFront+1..|Content|];
    } else {
      Content := [];
    }
  }

  method size() returns (size:nat)
    ensures size == counter
  {
    size := counter;
  }

  method isEmpty() returns (isEmpty: bool)
    ensures isEmpty == true ==> counter == 0;
    ensures isEmpty == false ==> counter != 0;
  {
    isEmpty := counter == 0;
  }

  method contains(item: int) returns (contains: bool)
    ensures contains == true ==> item in circularQueue[..]
    ensures contains == false ==> item !in circularQueue[..]
  {
    var i: nat := 0;
    contains := false;
    while (i < circularQueue.Length)
      invariant 0 <= i <= circularQueue.Length
      invariant contains ==> exists j :: 0 <= j < i && circularQueue[j] == item
      invariant !contains ==> forall j :: 0 <= j < i ==> circularQueue[j] != item
    {
      if (circularQueue[i] == item) {
        contains := true;
        break;
      }
      i := i + 1;
    }
  }

  method mergeQueues(otherQueue: Queue) returns (mergedQueue: Queue) 
  {
    var newQueueSize : int := otherQueue.circularQueue.Length + circularQueue.Length;
    var tmp: array<int> := new int[newQueueSize];
    var i: int := 0;
    while i < circularQueue.Length
      invariant 0 <= i <= circularQueue.Length
      invariant forall j :: 0 <= j < i ==> tmp[j] == circularQueue[j]
    { 
      tmp[i] := circularQueue[i];
      i := i + 1;
    }
    var j: int := 0;
    while j < otherQueue.circularQueue.Length
      invariant 0 <= j <= otherQueue.circularQueue.Length
      invariant forall k :: 0 <= k < j ==> tmp[circularQueue.Length + k] == otherQueue.circularQueue[k]
    {
      tmp[circularQueue.Length + j] := otherQueue.circularQueue[j];
      j := j + 1;
    }
    mergedQueue := new Queue();
    mergedQueue.circularQueue := tmp;
    mergedQueue.front := 0;
    mergedQueue.rear := newQueueSize;
    mergedQueue.counter := circularQueue.Length + otherQueue.circularQueue.Length;
    mergedQueue.Content := this.Content + otherQueue.Content;
  }
}

method Main ()
{
  var circularQueue := new Queue();

  var isQueueEmpty := circularQueue.isEmpty();

  var queueSize := circularQueue.size();

  circularQueue.auxInsertEmptyQueue(2);

  circularQueue.auxInsertEndQueue(4);

  circularQueue.auxInsertEndQueue(4);

  circularQueue.auxInsertEndQueue(56);

  var contains56 := circularQueue.contains(56);

  var contains4 := circularQueue.contains(4);

  var item := circularQueue.remove();
  //assert circularQueue.Content == [2, 4, 4, 56];
}

function abs(a: real) : real {if a>0.0 then a else -a}
