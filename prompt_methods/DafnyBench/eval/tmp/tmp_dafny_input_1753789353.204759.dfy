// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Composite {
  var left: Composite?
  var right: Composite?
  var parent: Composite?
  var val: int
  var sum: int

  function Valid(S: set<Composite>): bool
    reads this, parent, left, right
  {
    this in S &&
    (parent != null ==> parent in S && (parent.left == this || parent.right == this)) &&
    (left != null ==> left in S && left.parent == this && left != right) &&
    (right != null ==> right in S && right.parent == this && left != right) &&
    sum == val + (if left == null then 0 else left.sum) + (if right == null then 0 else right.sum)
  }

  function Acyclic(S: set<Composite>): bool
    reads S
  {
    this in S &&
    (parent != null ==> parent.Acyclic(S - {this}))
  }

  method Init(x: int)
    modifies this
    ensures Valid({this}) && Acyclic({this}) && val == x && parent == null
  {
    parent := null;
    left := null;
    right := null;
    val := x;
    sum := val;
  }

  method Update(x: int, ghost S: set<Composite>)
    requires this in S && Acyclic(S)
    requires forall c :: c in S ==> c.Valid(S)
    modifies S
    ensures forall c :: c in S ==> c.Valid(S)
    ensures forall c :: c in S ==> c.left == old(c.left) && c.right == old(c.right) && c.parent == old(c.parent)
    ensures forall c :: c in S && c != this ==> c.val == old(c.val)
    ensures val == x
  {
    var delta := x - val;
    val := x;
    // At this point, sum is not yet valid for this and its ancestors
    Adjust(delta, S, S);
  }

  method Add(ghost S: set<Composite>, child: Composite, ghost U: set<Composite>)
    requires this in S && Acyclic(S)
    requires forall c :: c in S ==> c.Valid(S)
    requires child in U
    requires forall c :: c in U ==> c.Valid(U)
    requires S !! U
    requires left == null || right == null
    requires child.parent == null
    modifies S, child
    ensures child.left == old(child.left) && child.right == old(child.right) && child.val == old(child.val)
    ensures forall c :: c in S && c != this ==> c.left == old(c.left) && c.right == old(c.right)
    ensures old(left) != null ==> left == old(left)
    ensures old(right) != null ==> right == old(right)
    ensures forall c :: c in S ==> c.parent == old(c.parent) && c.val == old(c.val)
    ensures child.parent == this
    ensures forall c: Composite {:autotriggers false} :: c in S+U ==> c.Valid(S+U)
  {
    if (left == null) {
      left := child;
    } else {
      right := child;
    }
    child.parent := this;
    // At this point, sum is not yet valid for this and its ancestors
    Adjust(child.sum, S, S+U);
  }

  method Dislodge(ghost S: set<Composite>)
    requires this in S && Acyclic(S)
    requires forall c :: c in S ==> c.Valid(S)
    modifies S
    ensures forall c :: c in S ==> c.Valid(S)
    ensures forall c :: c in S ==> c.val == old(c.val)
    ensures forall c :: c in S && c != this ==> c.parent == old(c.parent)
    ensures parent == null
    ensures forall c :: c in S ==> c.left == old(c.left) || (old(c.left) == this && c.left == null)
    ensures forall c :: c in S ==> c.right == old(c.right) || (old(c.right) == this && c.right == null)
    ensures Acyclic({this})
  {
    var p := parent;
    parent := null;
    if (p != null) {
      if (p.left == this) {
        p.left := null;
      } else {
        p.right := null;
      }
      var delta := -sum;
      p.Adjust(delta, S - {this}, S);
    }
  }

  /*private*/ method Adjust(delta: int, ghost U: set<Composite>, ghost S: set<Composite>)
    requires U <= S && Acyclic(U)
    requires forall c :: c in S && c != this ==> c.Valid(S)
    requires parent != null ==> parent in S && (parent.left == this || parent.right == this)
    requires left != null ==> left in S && left.parent == this && left != right
    requires right != null ==> right in S && right.parent == this && left != right
    requires sum + delta == val + (if left == null then 0 else left.sum) + (if right == null then 0 else right.sum)
    modifies U`sum
    ensures forall c :: c in S ==> c.Valid(S)
  {
    var p: Composite? := this;
    ghost var T := U;
    while (p != null)
      invariant p == null || p in T
      invariant T <= U
      invariant U <= S
      invariant forall c :: c in S && c != this ==> c.Valid(S)
      invariant forall q :: q in U - T ==> q.sum == old(q.sum) + delta
      invariant forall q :: q in T ==> q.sum + delta == q.val + (if q.left == null then 0 else q.left.sum) + (if q.right == null then 0 else q.right.sum)
      decreases if p == null then 0 else |T|
    {
      p.sum := p.sum + delta;
      T := T - {p};
      p := p.parent;
    }
    // After loop, all sum fields in U have been adjusted by delta, so all are valid
  }
}

method Main()
{
  var c0 := new Composite.Init(57);

  var c1 := new Composite.Init(12);
  c0.Add({c0}, c1, {c1});

  var c2 := new Composite.Init(48);

  var c3 := new Composite.Init(48);
  c2.Add({c2}, c3, {c3});
  c0.Add({c0,c1}, c2, {c2,c3});

  ghost var S := {c0, c1, c2, c3};
  c1.Update(100, S);
  c2.Update(102, S);

  c2.Dislodge(S);
  c2.Update(496, S);
  c0.Update(0, S);
}

method Harness() {
  var a := new Composite.Init(5);
  var b := new Composite.Init(7);
  a.Add({a}, b, {b});

  b.Update(17, {a,b});

  var c := new Composite.Init(10);
  b.Add({a,b}, c, {c});
  b.Dislodge({a,b,c});
}

function abs(a: real) : real {if a>0.0 then a else -a}
