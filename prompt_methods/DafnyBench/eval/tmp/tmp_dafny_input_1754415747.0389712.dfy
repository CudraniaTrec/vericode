
// RUN: %dafny /compile:0 /deprecation:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Here is the usual definition of possibly infinite lists, along with a function Tail(s, n), which drops
// n heads from s, and two lemmas that prove properties of Tail.

codatatype Stream<T> = Nil | Cons(head: T, tail: Stream)

ghost function Tail(s: Stream, n: nat): Stream
{
  if n == 0 then s else
    var t := Tail(s, n-1);
    if t == Nil then t else t.tail
}

lemma Tail_Lemma0(s: Stream, n: nat)
  requires s.Cons? && Tail(s, n).Cons?;
  ensures Tail(s, n).tail == Tail(s.tail, n);
{
  if n == 0 {
    // Tail(s, 0) == s, so Tail(s, 0).tail == s.tail == Tail(s.tail, 0)
    assert Tail(s, n).tail == s.tail;
    assert Tail(s.tail, n) == s.tail;
  } else {
    // Inductive step
    assert Tail(s, n) == if n == 0 then s else
      var t := Tail(s, n-1);
      if t == Nil then t else t.tail;
    var t := Tail(s, n-1);
    if t == Nil {
      assert Tail(s, n) == t;
      assert Tail(s, n).tail == t.tail;
      assert Tail(s.tail, n) == Tail(s.tail, n);
    } else {
      assert Tail(s, n) == t.tail;
      assert Tail(s, n).tail == t.tail.tail;
      Tail_Lemma0(s, n-1);
      assert t.tail.tail == Tail(s.tail, n-1).tail;
      assert Tail(s.tail, n) == if n == 0 then s.tail else
        var t2 := Tail(s.tail, n-1);
        if t2 == Nil then t2 else t2.tail;
      var t2 := Tail(s.tail, n-1);
      if t2 == Nil {
        assert Tail(s.tail, n) == t2;
      } else {
        assert Tail(s.tail, n) == t2.tail;
      }
    }
  }
}

lemma Tail_Lemma1(s: Stream, k: nat, n: nat)
  requires k <= n;
  ensures Tail(s, n).Cons? ==> Tail(s, k).Cons?;
  // Note, the contrapositive of this lemma says:  Tail(s, k) == Nil ==> Tail(s, n) == Nil
{
  if k == n {
    // Tail(s, n).Cons? ==> Tail(s, k).Cons? is trivial
  } else if k < n && Tail(s, n).Cons? {
    // Tail(s, n) is Cons
    if n == 0 {
      // Impossible, since k < n, so n > 0
      assert false;
    } else {
      var t := Tail(s, n-1);
      if t == Nil {
        // Tail(s, n) == Nil, contradiction to Cons?
        assert false;
      } else {
        // Tail(s, n) == t.tail
        Tail_Lemma1(s, k, n-1);
      }
    }
  }
}
lemma Tail_Lemma2(s: Stream, n: nat)
  requires s.Cons? && Tail(s.tail, n).Cons?;
  ensures Tail(s, n).Cons?;
{
  if n == 0 {
    // Tail(s, 0) == s, so s.Cons? holds
  } else {
    // Tail(s, n) == Tail(s, n-1).tail if Tail(s, n-1) != Nil
    Tail_Lemma0(s, n-1);
    if Tail(s, n-1) == Nil {
      // Tail(s, n) == Nil.tail == Nil, contradiction to ensures
      assert false;
    } else {
      // Tail(s, n) == Tail(s, n-1).tail
      Tail_Lemma2(s.tail, n-1);
    }
  }
}

// Co-predicate IsNeverEndingStream(s) answers whether or not s ever contains Nil.

greatest predicate IsNeverEndingStream<S>(s: Stream<S>)
{
  match s
  case Nil => false
  case Cons(_, tail) => IsNeverEndingStream(tail)
}

// Here is an example of an infinite stream.

ghost function AnInfiniteStream(): Stream<int>
{
  Cons(0, AnInfiniteStream())
}
greatest lemma Proposition0()
  ensures IsNeverEndingStream(AnInfiniteStream());
{
  // By coinduction, AnInfiniteStream() is always Cons, and its tail is AnInfiniteStream()
}

// Now, consider a Tree definition, where each node can have a possibly infinite number of children.

datatype Tree = Node(children: Stream<Tree>)

// Such a tree might have not just infinite width but also infinite height.  The following predicate
// holds if there is, for every path down from the root, a common bound on the height of each such path.
// Note that the definition needs a co-predicate in order to say something about all of a node's children.

ghost predicate HasBoundedHeight(t: Tree)
{
  exists n :: 0 <= n && LowerThan(t.children, n)
}
greatest predicate LowerThan(s: Stream<Tree>, n: nat)
{
  match s
  case Nil => true
  case Cons(t, tail) =>
    1 <= n && LowerThan(t.children, n-1) && LowerThan(tail, n)
}

// Co-predicate LowerThan(s, n) recurses on LowerThan(s.tail, n).  Thus, a property of LowerThan is that
// LowerThan(s, h) implies LowerThan(s', h) for any suffix s' of s.

lemma LowerThan_Lemma(s: Stream<Tree>, n: nat, h: nat)
  ensures LowerThan(s, h) ==> LowerThan(Tail(s, n), h);
{
  Tail_Lemma1(s, 0, n);
  if n == 0 || Tail(s, n) == Nil {
    // Base case: Tail(s, n) == s or == Nil
  } else {
    match s {
      case Cons(t, tail) =>
        LowerThan_Lemma(tail, n-1, h);
        Tail_Lemma0(s, n-1);
    }
  }
}

// A tree t where every node has an infinite number of children satisfies InfiniteEverywhere(t.children).
// Otherwise, IsFiniteSomewhere(t) holds.  That is, IsFiniteSomewhere says that the tree has some node
// with less than infinite width.  Such a tree may or may not be of finite height, as we'll see in an
// example below.

ghost predicate IsFiniteSomewhere(t: Tree)
{
  !InfiniteEverywhere(t.children)
}
greatest predicate InfiniteEverywhere(s: Stream<Tree>)
{
  match s
  case Nil => false
  case Cons(t, tail) => InfiniteEverywhere(t.children) && InfiniteEverywhere(tail)
}

// Here is a tree where every node has exactly 1 child.  Such a tree is finite in width (which implies
// it is finite somewhere) and infinite in height (which implies there is no bound on its height).

ghost function SkinnyTree(): Tree
{
  Node(Cons(SkinnyTree(), Nil))
}
lemma Proposition1()
  ensures IsFiniteSomewhere(SkinnyTree()) && !HasBoundedHeight(SkinnyTree());
{
  // IsFiniteSomewhere(SkinnyTree()) holds because the root has only one child (not infinite width)
  // !HasBoundedHeight(SkinnyTree()) because the height is infinite (no finite n such that LowerThan(children, n))
}

// Any tree where all paths have bounded height are finite somewhere.

lemma Theorem0(t: Tree)
  requires HasBoundedHeight(t);
  ensures IsFiniteSomewhere(t);
{
  var n :| 0 <= n && LowerThan(t.children, n);
  /*
    LowerThan(t.children, n) means that for every path down the tree, the path is at most n long.
    So, the tree cannot have infinite width everywhere.
  */
  var k := FindNil(t.children, n);
}
lemma FindNil(s: Stream<Tree>, n: nat) returns (k: nat)
  requires LowerThan(s, n);
  ensures !InfiniteEverywhere#[k as ORDINAL](s);
{
  match s {
    case Nil => k := 1;
    case Cons(t, _) =>
	  k := FindNil(t.children, n-1);
	  k := k + 1;
  }
}

// We defined an InfiniteEverywhere property above and negated it to get an IsFiniteSomewhere predicate.
// If we had an InfiniteHeightSomewhere property, then we could negate it to obtain a predicate
// HasFiniteHeightEverywhere.  Consider the following definitions:

ghost predicate HasFiniteHeightEverywhere_Bad(t: Tree)
{
  !InfiniteHeightSomewhere_Bad(t.children)
}
greatest predicate InfiniteHeightSomewhere_Bad(s: Stream<Tree>)
{
  match s
  case Nil => false
  case Cons(t, tail) => InfiniteHeightSomewhere_Bad(t.children) || InfiniteHeightSomewhere_Bad(tail)
}

// In some ways, this definition may look reasonable--a list of trees is infinite somewhere
// if it is nonempty, and either the list of children of the first node satisfies the property
// or the tail of the list does.  However, because co-predicates are defined by greatest
// fix-points, there is nothing in this definition that "forces" the list to ever get to a
// node whose list of children satisfy the property.  The following example shows that a
// shallow, infinitely wide tree satisfies the negation of HasFiniteHeightEverywhere_Bad.

ghost function ATree(): Tree
{
  Node(ATreeChildren())
}
ghost function ATreeChildren(): Stream<Tree>
{
  Cons(Node(Nil), ATreeChildren())
}
lemma Proposition2()
  ensures !HasFiniteHeightEverywhere_Bad(ATree());
{
  Proposition2_Lemma0();
  Proposition2_Lemma1(ATreeChildren());
}
greatest lemma Proposition2_Lemma0()
  ensures IsNeverEndingStream(ATreeChildren());
{
  // By coinduction, ATreeChildren() is always Cons, and its tail is ATreeChildren()
}
greatest lemma Proposition2_Lemma1(s: Stream<Tree>)
  requires IsNeverEndingStream(s);
  ensures InfiniteHeightSomewhere_Bad(s);
{
  calc {
    InfiniteHeightSomewhere_Bad#[_k](s);
    InfiniteHeightSomewhere_Bad#[_k-1](s.head.children) || InfiniteHeightSomewhere_Bad#[_k-1](s.tail);
  <==
    InfiniteHeightSomewhere_Bad#[_k-1](s.tail);  // induction hypothesis
  }
}

// What was missing from the InfiniteHeightSomewhere_Bad definition was the existence of a child
// node that satisfies the property recursively.  To address that problem, we may consider
// a definition like the following:

/*
ghost predicate HasFiniteHeightEverywhere_Attempt(t: Tree)
{
  !InfiniteHeightSomewhere_Attempt(t.children)
}
greatest predicate InfiniteHeightSomewhere_Attempt(s: Stream<Tree>)
{
  exists n ::
    0 <= n &&
    var ch := Tail(s, n);
    ch.Cons? && InfiniteHeightSomewhere_Attempt(ch.head.children)
}
*/

// However, Dafny does not allow this definition:  the recursive call to InfiniteHeightSomewhere_Attempt
// sits inside an unbounded existential quantifier, which means the co-predicate's connection with its prefix
// predicate is not guaranteed to hold, so Dafny disallows this co-predicate definition.

// We will use a different way to express the HasFiniteHeightEverywhere property.  Instead of
// using an existential quantifier inside the recursively defined co-predicate, we can place a "larger"
// existential quantifier outside the call to the co-predicate.  This existential quantifier is going to be
// over the possible paths down the tree (it is "larger" in the sense that it selects a child tree at each
// level down the path, not just at one level).

// A path is a possibly infinite list of indices, each selecting the next child tree to navigate to.  A path
// is valid when it uses valid indices and does not stop at a node with children.

greatest predicate ValidPath(t: Tree, p: Stream<int>)
{
  match p
  case Nil => t == Node(Nil)
  case Cons(index, tail) =>
    0 <= index &&
    var ch := Tail(t.children, index);
    ch.Cons? && ValidPath(ch.head, tail)
}
lemma ValidPath_Lemma(p: Stream<int>)
  ensures ValidPath(Node(Nil), p) ==> p == Nil;
{
  if ValidPath(Node(Nil), p) {
    match p {
      case Nil =>
      case Cons(index, tail) =>  // proof by contradiction
        var nil : Stream<Tree> := Nil;
        Tail_Lemma1(nil, 0, index);
        // Tail(nil, index).Cons? cannot hold
        assert false;
    }
  }
}

// A tree has finite height (everywhere) if it has no valid infinite paths.

ghost predicate HasFiniteHeight(t: Tree)
{
  forall p :: ValidPath(t, p) ==> !IsNeverEndingStream(p)
}

// From this definition, we can prove that any tree of bounded height is also of finite height.

lemma Theorem1(t: Tree)
  requires HasBoundedHeight(t);
  ensures HasFiniteHeight(t);
{
  var n :| 0 <= n && LowerThan(t.children, n);
  forall p | ValidPath(t, p) 
    ensures !IsNeverEndingStream(p)
  {
    Theorem1_Lemma(t, n, p);
  }
}
lemma Theorem1_Lemma(t: Tree, n: nat, p: Stream<int>)
  requires LowerThan(t.children, n) && ValidPath(t, p);
  ensures !IsNeverEndingStream(p);
{
  match p {
    case Nil =>
      // IsNeverEndingStream(Nil) == false
    case Cons(index, tail) =>
      var ch := Tail(t.children, index);
      calc {
        LowerThan(t.children, n);
      ==>  { LowerThan_Lemma(t.children, index, n); }
        LowerThan(ch, n);
      ==>  // def. LowerThan
        LowerThan(ch.head.children, n-1);
      }
      // ValidPath(ch.head, tail)
      Theorem1_Lemma(ch.head, n-1, tail);
      // IsNeverEndingStream(tail) == false
      // So IsNeverEndingStream(p) == false
  }
}

// In fact, HasBoundedHeight is strictly strong than HasFiniteHeight, as we'll show with an example.
// Define SkinnyFiniteTree(n) to be a skinny (that is, of width 1) tree of height n.

ghost function SkinnyFiniteTree(n: nat): Tree
  ensures forall k: nat :: LowerThan(SkinnyFiniteTree(n).children, k) <==> n <= k;
{
  if n == 0 then Node(Nil) else Node(Cons(SkinnyFiniteTree(n-1), Nil))
}

// Next, we define a tree whose root has an infinite number of children, child i of which
// is a SkinnyFiniteTree(i).

ghost function FiniteUnboundedTree(): Tree
{
  Node(EverLongerSkinnyTrees(0))
}
ghost function EverLongerSkinnyTrees(n: nat): Stream<Tree>
{
  Cons(SkinnyFiniteTree(n), EverLongerSkinnyTrees(n+1))
}

lemma EverLongerSkinnyTrees_Lemma(k: nat, n: nat)
  ensures Tail(EverLongerSkinnyTrees(k), n).Cons?;
  ensures Tail(EverLongerSkinnyTrees(k), n).head == SkinnyFiniteTree(k+n);
{
  if n == 0 {
    // Tail(EverLongerSkinnyTrees(k), 0) == EverLongerSkinnyTrees(k)
    assert Tail(EverLongerSkinnyTrees(k), n).Cons?;
    assert Tail(EverLongerSkinnyTrees(k), n).head == SkinnyFiniteTree(k+n);
  } else {
    calc {
      Tail(EverLongerSkinnyTrees(k), n);
      { EverLongerSkinnyTrees_Lemma(k, n-1); }  // this ensures that .tail on the next line is well-defined
      Tail(EverLongerSkinnyTrees(k), n-1).tail;
      { Tail_Lemma0(EverLongerSkinnyTrees(k), n-1); }
      Tail(EverLongerSkinnyTrees(k).tail, n-1);
      Tail(EverLongerSkinnyTrees(k+1), n-1);
    }
    EverLongerSkinnyTrees_Lemma(k+1, n-1);
  }
}

lemma Proposition3()
  ensures !HasBoundedHeight(FiniteUnboundedTree()) && HasFiniteHeight(FiniteUnboundedTree());
{
  Proposition3a();
  Proposition3b();
}
lemma Proposition3a()
  ensures !HasBoundedHeight(FiniteUnboundedTree());
{
  var ch := FiniteUnboundedTree().children;
  forall n | 0 <= n
    ensures !LowerThan(ch, n);
  {
    var cn := Tail(ch, n+1);
    EverLongerSkinnyTrees_Lemma(0, n+1);
    LowerThan_Lemma(ch, n+1, n);
    // LowerThan(cn, n) does not hold because SkinnyFiniteTree(n+1) has children of height n+1
  }
}
lemma Proposition3b()
  ensures HasFiniteHeight(FiniteUnboundedTree());
{
  var t := FiniteUnboundedTree();
  forall p | ValidPath(t, p)
    ensures !IsNeverEndingStream(p);
  {
    var index := p.head;
    var ch := Tail(t.children, index);
    EverLongerSkinnyTrees_Lemma(0, index);
    var si := SkinnyFiniteTree(index);
    Proposition3b_Lemma(si, index, p.tail);
  }
}
lemma Proposition3b_Lemma(t: Tree, h: nat, p: Stream<int>)
  requires LowerThan(t.children, h) && ValidPath(t, p)
  ensures !IsNeverEndingStream(p)
{
  match p {
    case Nil =>
      // IsNeverEndingStream(Nil) == false
    case Cons(index, tail) =>
      // From the definition of ValidPath(t, p), we get the following:
      var ch := Tail(t.children, index);
      // assert ch.Cons? && ValidPath(ch.head, tail);
      // From the definition of LowerThan(t.children, h), we get the following:
      match t.children {
        case Nil =>
          ValidPath_Lemma(p);
        case Cons(_, _) =>
          // assert 1 <= h;
          LowerThan_
function abs(a: real) : real {if a>0.0 then a else -a}
