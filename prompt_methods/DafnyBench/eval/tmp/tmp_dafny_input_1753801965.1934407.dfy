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
    // No assertions here, only field assignments allowed before 'new;' division
  }

  method Rotate()
    requires Valid()
    requires 0 < |contents|
    modifies footprint
    ensures Valid() && fresh(footprint - old(footprint))
    ensures contents == old(contents)[1..] + old(contents)[..1]
  {
    assert Valid();
    assert 0 < |contents|;
    var t := Front();
    assert t == contents[0];
    Dequeue();
    assert contents == old(contents)[1..];
    Enqueue(t);
    assert contents == old(contents)[1..] + [t];
    assert old(contents)[..1] == [old(contents)[0]];
    assert contents == old(contents)[1..] + old(contents)[..1];
    assert Valid();
    assert fresh(footprint - old(footprint));
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
    assert Valid();
    assert 0 < |contents|;
    var t := Front();
    assert t == contents[0];
    Dequeue();
    assert contents == old(contents)[1..];
    Enqueue(t);
    assert contents == old(contents)[1..] + [t];
    assert |contents| == |old(contents)|;
    assert exists i :: 0 <= i && i <= |contents| && contents == old(contents)[i..] + old(contents)[..i];
    assert Valid();
    assert fresh(footprint - old(footprint));
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

    // Update all nodes in spine for tailContents and footprint
    var ss := spine;
    var oldTailContents := map m: Node<T> {:trigger m in ss} | m in ss :: m.tailContents;
    var oldFootprints := map m: Node<T> {:trigger m in ss} | m in ss :: m.footprint;

    var it := ss;
    while it != {}
      invariant it <= spine
      invariant ss == spine
      invariant forall m: Node<T> :: m in ss - it ==> m.tailContents == oldTailContents[m] + [t]
      invariant forall m: Node<T> :: m in ss - it ==> m.footprint == oldFootprints[m] + n.footprint
      decreases |it|
    {
      var m: Node<T> :| m in it;
      m.tailContents := m.tailContents + [t];
      m.footprint := m.footprint + n.footprint;
      it := it - {m};
    }

    contents := head.tailContents;
    footprint := footprint + n.footprint;
    spine := spine + {n};

    assert Valid();
    assert fresh(footprint - old(footprint));
    assert contents == old(contents) + [t];
  }

  method Front() returns (t: T)
    requires Valid()
    requires 0 < |contents|
    ensures t == contents[0]
  {
    assert head.next != null;
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
    assert head.next != null;
    var n := head.next;
    head := n;
    contents := n.tailContents;
    assert contents == old(contents)[1..];
    assert Valid();
    assert fresh(footprint - old(footprint));
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
    // No assertions here, only field assignments allowed before 'new;' division
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
    assert w == t;
    q0.Dequeue();
    assert q0.contents == [u];

    w := q0.Front();
    assert w == u;
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
    assert q0.Valid();
    assert q1.Valid();
    assert q0.footprint !! q1.footprint;
    assert |q0.contents| == 0;

    q0.Enqueue(t);
    assert q0.contents == [t];
    q0.Enqueue(u);
    assert q0.contents == [t, u];

    q1.Enqueue(v);
    assert q1.contents == [v];

    var w := q0.Front();
    assert w == t;
    q0.Dequeue();
    assert q0.contents == [u];

    w := q0.Front();
    assert w == u;

    assert fresh(q0.footprint - old(q0.footprint));
    assert fresh(q1.footprint - old(q1.footprint));
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
