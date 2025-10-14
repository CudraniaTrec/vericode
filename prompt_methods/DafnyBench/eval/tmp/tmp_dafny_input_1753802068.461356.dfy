
class Tree {
  // an empty tree is represented by a Tree object with left==this==right
  var value: int
  var left: Tree?
  var right: Tree?

  ghost var Contents: seq<int>
  ghost var Repr: set<object>
  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr &&
    left != null && right != null &&
    ((left == this == right && Contents == []) ||
     (left in Repr && left.Repr <= Repr && this !in left.Repr &&
      right in Repr && right.Repr <= Repr && this !in right.Repr &&
      left.Valid() && right.Valid() &&
      Contents == left.Contents + [value] + right.Contents))
  }

  function IsEmpty(): bool
    requires Valid();
    reads this, Repr;
    ensures IsEmpty() <==> Contents == [];
  {
    left == this
  }

  constructor Empty()
    ensures Valid() && Contents == [];
  {
    left, right := this, this;
    Contents := [];
    Repr := {this};
  }

  constructor Node(lft: Tree, val: int, rgt: Tree)
    requires lft.Valid() && rgt.Valid();
    ensures Valid() && Contents == lft.Contents + [val] + rgt.Contents;
  {
    left, value, right := lft, val, rgt;
    Contents := lft.Contents + [val] + rgt.Contents;
    Repr := lft.Repr + {this} + rgt.Repr;
  }

  lemma exists_intro<T>(P: T ~> bool, x: T)
    requires P.requires(x)
    requires P(x)
    ensures exists y :: P.requires(y) && P(y)
  {
  }

  method ComputeMax() returns (mx: int)
    requires Valid() && !IsEmpty();
    ensures forall x :: x in Contents ==> x <= mx;
    ensures exists x :: x in Contents && x == mx;
  {
    // Strongest possible annotations

    // At entry: Valid() && !IsEmpty()
    // Contents == left.Contents + [value] + right.Contents
    // left.Valid(), right.Valid()
    // left != null, right != null

    mx := value;

    // Invariant: mx is the maximum of value and all already-visited subtrees

    if (!left.IsEmpty()) 
      // left.Valid() && !left.IsEmpty()
      // left.Contents != []
      // left.Contents subset of Contents
      // mx == value
    {
      var m := left.ComputeMax();
      // assert forall x :: x in left.Contents ==> x <= m;
      // assert exists x :: x in left.Contents && x == m;
      // assert forall x :: x in left.Contents ==> x <= m <= mx || x <= mx;
      // assert left.Contents + [value] + right.Contents == Contents;
      // assert m >= mx || m <= mx;
      mx := if mx < m  then m else mx;
      // assert forall x :: x in left.Contents + [value] ==> x <= mx;
      // assert exists x :: x in left.Contents + [value] && x == mx;
    }

    if (!right.IsEmpty()) 
      // right.Valid() && !right.IsEmpty()
      // right.Contents != []
      // right.Contents subset of Contents
      // mx is max of value and left subtree
    {
      var m := right.ComputeMax();
      // assert forall x :: x in right.Contents ==> x <= m;
      // assert exists x :: x in right.Contents && x == m;
      mx := if mx < m then m else mx;
      // assert forall x :: x in left.Contents + [value] + right.Contents ==> x <= mx;
    }

    // At this point, mx is the maximum of all elements in Contents
    // assert forall x :: x in Contents ==> x <= mx;
    // assert exists x :: x in Contents && x == mx;

    exists_intro(x reads this => x in Contents && x == mx, mx);
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
