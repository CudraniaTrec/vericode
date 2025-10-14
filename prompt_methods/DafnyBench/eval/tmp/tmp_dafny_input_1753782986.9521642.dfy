
class {:autocontracts} Queue {

  // Atributos
  var circularQueue: array<int>;
  var rear: nat;  // cauda
  var front: nat; // head
  var counter: nat;

  // Abstração
  ghost var Content: seq<int>;

  // Predicado
  ghost predicate Valid()
  {
    0 <= counter <= circularQueue.Length &&
    0 <= front &&
    0 <= rear &&
    Content == circularQueue[..]
  }

  // Construtor
  constructor()
    ensures circularQueue.Length == 0
    ensures front == 0 && rear == 0
    ensures Content == [] // REVISAR
    ensures counter == 0
  {
    circularQueue := new int[0];
    rear := 0;
    front := 0;
    Content := [];
    counter := 0;
  } //[tam] ; [1, 2, 3, 4]

  method insert(item: int)
    // requires rear <= circularQueue.Length
    // ensures (front == 0 && rear == 0 && circularQueue.Length == 1) ==>
    //     (
    //       Content == [item] &&
    //       |Content| == 1
    //     )
    // ensures circularQueue.Length != 0 ==>
    // (
    //   (front == 0 && rear == 0 && circularQueue.Length == 1) ==>
    //     (
    //       Content == old(Content)  &&
    //       |Content| == old(|Content|)

    //     )
    // ||
    //   (front == 0 && rear == circularQueue.Length-1 ) ==> 
    //     (
    //       Content == old(Content) + [item] &&
    //       |Content| == old(|Content|) + 1
    //     )
    // ||
    //   (rear + 1 != front && rear != circularQueue.Length-1 && rear + 1 < circularQueue.Length - 1) ==> 
    //     (
    //       Content == old(Content[0..rear]) + [item] + old(Content[rear..circularQueue.Length])
    //     )
    // ||
    //   (rear + 1 == front) ==> 
    //   (
    //     Content[0..rear + 1] == old(Content[0..rear]) + [item] &&
    //     forall i :: rear + 2 <= i <= circularQueue.Length ==> Content[i] == old(Content[i-1])
    //   )
    // )
    {
      // Strongest possible annotation for this method:
      //assert Valid();
      if front == 0 && rear == 0 && circularQueue.Length == 0
      {
        //assert counter == 0;
        //assert Content == [];
        //assert circularQueue.Length == 0;
        auxInsertEmptyQueue(item);
        //assert Content == [item];
        //assert rear == 1;
        //assert counter == 1;
      }   
      else if front == 0 && rear == circularQueue.Length && circularQueue.Length >= 1
      {
        //assert Content == circularQueue[..];
        //assert rear == circularQueue.Length;
        //assert front == 0;
        auxInsertEndQueue(item);
        //assert Content == old(Content) + [item];
        //assert rear == old(rear) + 1;
        //assert counter == old(counter) + 1;
      }
      else if rear < front && front < circularQueue.Length
      {
        //assert rear < front;
        //assert front < circularQueue.Length;
        auxInsertSpaceQueue(item);
        //assert rear == old(rear) + 1;
        //assert counter == old(counter) + 1;
        //assert Content == old(Content[0..rear]) + [item] + old(Content[rear+1..circularQueue.Length]);
      }
      else if rear + 1 == front
      {
        auxInsertBetweenQueue(item);
      }
      else
      {
        //assert false; // Should not reach here
      }
      //assert Valid();
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
    queueInsert := new int [circularQueue.Length + 1];
    queueInsert[0] := item;
    circularQueue := queueInsert;
    Content := [item];
    rear := rear + 1;
    //assert circularQueue.Length == 1;
    //assert Content == [item];
    //assert rear == 1;
    //assert counter == old(counter) + 1;
    //assert front == 0;
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
    Content := Content + [item];
    rear := rear + 1;
    circularQueue := queueInsert;
    //assert Content == old(Content) + [item];
    //assert |Content| == old(|Content|) + 1;
    //assert rear == old(rear) + 1;
    //assert counter == old(counter) + 1;
    //assert front == 0;
  }

  method auxInsertSpaceQueue(item:int)
    requires rear < front && front < circularQueue.Length
    ensures rear == old(rear) + 1
    ensures counter == old(counter) + 1
    ensures Content == old(Content[0..rear]) + [item] + old(Content[rear+1..circularQueue.Length])
    ensures |Content| == old(|Content|) + 1
  {
    counter := counter + 1;
    //assert rear < front;
    //assert front < circularQueue.Length;
    // Insert item at position rear
    circularQueue[rear] := item;
    Content := old(Content[0..rear]) + [item] + old(Content[rear+1..circularQueue.Length]);
    rear := rear + 1;
    //assert rear == old(rear) + 1;
    //assert counter == old(counter) + 1;
    //assert Content == old(Content[0..old(rear)]) + [item] + old(Content[old(rear)+1..circularQueue.Length]);
    //assert |Content| == old(|Content|) + 1;
  }

  method auxInsertInitQueue(item:int)
    // strongest annotation possible:
    // requires ?
    // ensures ?
  {
    // Implementation not provided
    //assert true;
  }

  method auxInsertBetweenQueue(item:int)
    // strongest annotation possible:
    // requires ?
    // ensures ?
  {
    // Implementation not provided
    //assert true;
  }

  // remove apenas mudando o ponteiro
  // sem resetar o valor na posição, pois, provavelmente,
  // vai ser sobrescrito pela inserção
  method remove() returns (item: int)
    requires front < circularQueue.Length
    requires circularQueue.Length > 0
    ensures rear <= |old(Content)|
    ensures circularQueue.Length > 0
    ensures item == old(Content)[old(front)]
    ensures front == (old(front) + 1) % circularQueue.Length
    ensures old(front) < rear ==> Content == old(Content)[old(front)..rear]
    ensures old(front) > rear ==> Content == old(Content)[0 .. rear] + old(Content)[old(front)..|old(Content)|]
  {
    //assert front < circularQueue.Length;
    //assert circularQueue.Length > 0;
    if counter == 0 {
      item := -1;
      //assert item == -1;
    } else {
      item := circularQueue[front];
      var oldFront := front;
      front := (front + 1) % circularQueue.Length;
      counter := counter - 1;
      if oldFront < rear {
        Content := old(Content)[oldFront..rear];
        //assert Content == old(Content)[oldFront..rear];
      } else if oldFront > rear {
        Content := old(Content)[0..rear] + old(Content)[oldFront..|old(Content)|];
        //assert Content == old(Content)[0..rear] + old(Content)[oldFront..|old(Content)|];
      }
      //assert item == old(Content)[oldFront];
      //assert front == (oldFront + 1) % circularQueue.Length;
    }
    //assert circularQueue.Length > 0;
  }

  method size() returns (size:nat)
    ensures size == counter
  {
    size := counter;
    //assert size == counter;
  }

  method isEmpty() returns (isEmpty: bool)
    ensures isEmpty == true ==> counter == 0;
    ensures isEmpty == false ==> counter != 0;
  {
    isEmpty := if counter == 0 then true else false;
    //assert (isEmpty == true ==> counter == 0);
    //assert (isEmpty == false ==> counter != 0);
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
    //assert contains == true ==> item in circularQueue[..];
    //assert contains == false ==> item !in circularQueue[..];
  }

  // TODO
  method mergeQueues(otherQueue: Queue) returns (mergedQueue: Queue) 
  {
    
    // queue1.merge(queue2)
    var newQueueSize : int := otherQueue.circularQueue.Length + circularQueue.Length;
    var newFront: int := front;
    var newRear: int := otherQueue.rear;

    var tmp: array<int> := new int[newQueueSize];

    var i: int;
    i := 0;
    while i < circularQueue.Length
      invariant 0 <= i <= circularQueue.Length
      invariant forall j :: 0 <= j < i ==> tmp[j] == circularQueue[j]
    { 
      tmp[i] := circularQueue[i];
      i := i + 1;
    }

    // vamos copiar valores vazios?
    // como identificamos os vazios? entre o rear e o front
    // como iteramos entre rear e front? front -> rear
    // [1, 3, 5, 7, 9] + [0, 2, 4, 6, 8] => [0, 2, 4, 6, 8, 1, 3, 5, 7, 9]
    // front => 8 
    // rear => 0
    
    mergedQueue := new Queue(); 
    //assert mergedQueue != null;
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
