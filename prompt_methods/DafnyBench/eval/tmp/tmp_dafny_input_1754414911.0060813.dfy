
// RUN: %testDafnyForEachResolver "%s"


// Queue.dfy
// Dafny version of Queue.bpl
// Rustan Leino, 2008

class Queue<T(0)> {
  var head: Node<T>
  var tail: Node<T>

  ghost var contents: seq<T>
  ghost var footprint: set<object>
  ghost var spine: set<Node<T>>

  ghost predicate Valid()
    reads this, footprint
  {
    this in footprint && spine <= footprint &&
    head in spine &&
    tail in spine &&
    tail.next == null &&
    (forall n ::
      n in spine ==>
        n.footprint <= footprint && this !in n.footprint &&
        n.Valid() &&
        (n.next == null ==> n == tail)) &&
    (forall n ::
      n in spine ==>
        n.next != null ==> n.next in spine) &&
    contents == head.tailContents
  }

  constructor Init()
    ensures Valid() && fresh(footprint - {this})
    ensures |contents| == 0
  {
    var n: Node<T> := new Node<T>.Init();
    head := n;
    tail := n;
    contents := n.tailContents;
    footprint := {this} + n.footprint;
    spine := {n};
    // Strongest post-state: head == tail, contents == [], spine == {n}, n.tailContents == [], n.Valid(), footprint == {this, n}
    assert head == tail;
    assert contents == [];
    assert spine == {n};
    assert n.tailContents == [];
    assert n.Valid();
    assert footprint == {this, n};
    assert Valid();
  }

  method Rotate()
    requires Valid()
    requires 0 < |contents|
    modifies footprint
    ensures Valid() && fresh(footprint - old(footprint))
    ensures contents == old(contents)[1..] + old(contents)[..1]
  {
    // Strongest invariant: Valid() && |contents| == |old(contents)| && contents == old(contents)[1..] + [old(contents)[0]]
    var t := Front();
    assert t == contents[0];
    Dequeue();
    assert contents == old(contents)[1..];
    Enqueue(t);
    assert contents == old(contents)[1..] + [old(contents)[0]];
    assert Valid();
  }

  method RotateAny()
    requires Valid()
    requires 0 < |contents|
    modifies footprint
    ensures Valid() && fresh(footprint - old(footprint))
    ensures |contents| == |old(contents)|
    ensures exists i :: 0 <= i && i <= |contents| &&
              contents == old(contents)[i..] + old(contents)[..i]
  {
    // This implementation rotates by 1, so i == 1
    var t := Front();
    assert t == contents[0];
    Dequeue();
    assert contents == old(contents)[1..];
    Enqueue(t);
    assert contents == old(contents)[1..] + [old(contents)[0]];
    assert |contents| == |old(contents)|;
    assert exists i :: 0 <= i && i <= |contents| && contents == old(contents)[i..] + old(contents)[..i];
    assert Valid();
  }

  method IsEmpty() returns (isEmpty: bool)
    requires Valid()
    ensures isEmpty <==> |contents| == 0
  {
    isEmpty := head == tail;
    assert (isEmpty <==> |contents| == 0);
  }

  method Enqueue(t: T)
    requires Valid()
    modifies footprint
    ensures Valid() && fresh(footprint - old(footprint))
    ensures contents == old(contents) + [t]
  {
    var n := new Node<T>.Init();
    n.data := t;
    tail.next := n;
    tail := n;

    // Invariant: for all m in spine, m.tailContents == old(m.tailContents) + [t]
    forall m | m in spine
      ensures m.tailContents == old(m.tailContents) + [t]
    {
      m.tailContents := m.tailContents + [t];
    }
    contents := head.tailContents;

    forall m | m in spine
      ensures m.footprint == old(m.footprint) + n.footprint
    {
      m.footprint := m.footprint + n.footprint;
    }
    footprint := footprint + n.footprint;

    spine := spine + {n};
    assert contents == old(contents) + [t];
    assert Valid();
  }

  method Front() returns (t: T)
    requires Valid()
    requires 0 < |contents|
    ensures t == contents[0]
  {
    t := head.next.data;
    assert t == contents[0];
  }

  method Dequeue()
    requires Valid()
    requires 0 < |contents|
    modifies footprint
    ensures Valid() && fresh(footprint - old(footprint))
    ensures contents == old(contents)[1..]
  {
    var n := head.next;
    head := n;
    contents := n.tailContents;
    assert contents == old(contents)[1..];
    assert Valid();
  }
}

class Node<T(0)> {
  var data: T
  var next: Node?<T>

  ghost var tailContents: seq<T>
  ghost var footprint: set<object>

  ghost predicate Valid()
    reads this, footprint
  {
    this in footprint &&
    (next != null ==> next in footprint && next.footprint <= footprint) &&
    (next == null ==> tailContents == []) &&
    (next != null ==> tailContents == [next.data] + next.tailContents)
  }

  constructor Init()
    ensures Valid() && fresh(footprint - {this})
    ensures next == null
  {
    next := null;
    tailContents := [];
    footprint := {this};
    assert next == null;
    assert tailContents == [];
    assert footprint == {this};
    assert Valid();
  }
}

class Main<U(0)> {
  method A<T(0)>(t: T, u: T, v: T)
  {
    var q0 := new Queue<T>.Init();
    var q1 := new Queue<T>.Init();

    q0.Enqueue(t);
    assert q0.contents == [t];
    q0.Enqueue(u);
    assert q0.contents == [t, u];

    q1.Enqueue(v);
    assert q1.contents == [v];


    var w := q0.Front();
    assert w == q0.contents[0];
    q0.Dequeue();
    assert q0.contents == [u];

    w := q0.Front();
    assert w == q0.contents[0];

  }

  method Main2(t: U, u: U, v: U, q0: Queue<U>, q1: Queue<U>)
    requires q0.Valid()
    requires q1.Valid()
    requires q0.footprint !! q1.footprint
    requires |q0.contents| == 0
    modifies q0.footprint, q1.footprint
    ensures fresh(q0.footprint - old(q0.footprint))
    ensures fresh(q1.footprint - old(q1.footprint))
  {
    q0.Enqueue(t);
    assert q0.contents == [t];
    q0.Enqueue(u);
    assert q0.contents == [t, u];

    q1.Enqueue(v);
    assert q1.contents == [v];


    var w := q0.Front();
    assert w == q0.contents[0];
    q0.Dequeue();
    assert q0.contents == [u];

    w := q0.Front();
    assert w == q0.contents[0];

  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
