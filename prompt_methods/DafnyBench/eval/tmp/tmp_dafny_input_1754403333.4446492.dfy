// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Node {
  var left: Node?
  var right: Node?
  var parent: Node?
  var anc: set<Node>
  var desc: set<Node>
  var sense: bool
  var pc: int

  predicate validDown()
    reads this, desc
  {
    this !in desc &&
    left != right &&  // not needed, but speeds up verification

    (right != null ==> right in desc && left !in right.desc) &&

    (left != null ==>
      left in desc &&
      (right != null ==> desc == {left,right} + left.desc + right.desc)  &&
      (right == null ==> desc == {left} + left.desc)  &&
      left.validDown()) &&
    (left == null ==>
      (right != null ==> desc == {right} + right.desc)  &&
      (right == null ==> desc == {})) &&

    (right != null ==> right.validDown()) &&

    (blocked() ==> forall m :: m in desc ==> m.blocked()) &&
    (after() ==> forall m :: m in desc ==> m.blocked() || m.after())
//    (left != null && right != null ==> left.desc !! right.desc)  // not needed
  }

  predicate validUp()
    reads this, anc
  {
    this !in anc &&
    (parent != null ==> parent in anc && anc == { parent } + parent.anc && parent.validUp()) &&
    (parent == null ==> anc == {}) &&
    (after() ==> forall m :: m in anc ==> m.after())
  }

  predicate valid()
    reads this, desc, anc
  { validUp() && validDown() && desc !! anc }

  predicate before()
    reads this
  { !sense && pc <= 2 }

  predicate blocked()
    reads this
  { sense }

  predicate after()
    reads this
  { !sense && 3 <= pc }

  method barrier()
    requires valid()
    requires before()
    modifies this, left, right
  {
    //A
    pc := 1;
    if(left != null) {
      var oldSense := left.sense;
      while(!left.sense)
        modifies left
        decreases *
        invariant left != null
        invariant left.valid()
        invariant left.before() || left.blocked()
        invariant valid()
        invariant left in desc
        invariant forall m :: m in left.desc ==> m.valid()
        invariant left.sense == oldSense || left.sense
      {
        left.sense := *;
        assume left.blocked() ==> forall m :: m in left.desc ==> m.blocked();
      }
      assert left.sense;
    }
    if(right != null) {
      var oldSense := right.sense;
      while(!right.sense)
        modifies right
        decreases *
        invariant right != null
        invariant right.valid()
        invariant right.before() || right.blocked()
        invariant valid()
        invariant right in desc
        invariant forall m :: m in right.desc ==> m.valid()
        invariant right.sense == oldSense || right.sense
      {
        right.sense := *;
        assume right.blocked() ==> forall m :: m in right.desc ==> m.blocked();
      }
      assert right.sense;
    }

    //B
    pc := 2;
    if(parent != null) {
      sense := true;
      assert blocked();
    }
    //C
    pc := 3;
    var oldSense := sense;
    while(sense)
        modifies this
        decreases *
        invariant valid()
        invariant blocked() || after()
        invariant pc == 3
        invariant parent == null || parent.after()
        invariant sense || !sense
        invariant oldSense || !sense
    {
      sense := *;
      assume !sense ==> parent.after();
    }
    assert !sense;
    assert after();
    //D
    pc := 4;
    if(left != null) {
      left.sense := false;
      assert !left.sense;
      assert left.valid();
    }
    //E
    pc := 5;
    if(right != null) {
      right.sense := false;
      assert !right.sense;
      assert right.valid();
    }
    //F
    pc := 6;
    assert valid();
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
