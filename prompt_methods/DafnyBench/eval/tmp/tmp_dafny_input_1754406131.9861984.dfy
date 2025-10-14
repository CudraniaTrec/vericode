module Rope {
class Rope {
ghost var Contents: string;
ghost var Repr: set<Rope>;

var data: string;
var weight: nat;
var left: Rope?;
var right: Rope?;

ghost predicate Valid() 
    reads this, Repr
    ensures Valid() ==> this in Repr
{
    this in Repr &&
    (left != null ==> 
        left in Repr &&
        left.Repr < Repr && this !in left.Repr &&
        left.Valid() &&
        (forall child :: child in left.Repr ==> child.weight <= weight)) &&
    (right != null ==> 
        right in Repr &&
        right.Repr < Repr && this !in right.Repr &&
        right.Valid()) &&
    (left == null && right == null ==>
        Repr == {this} &&
        Contents == data &&
        weight == |data| &&
        data != "") &&
    (left != null && right == null ==>
        Repr == {this} + left.Repr &&
        Contents == left.Contents &&
        weight == |left.Contents| &&
        data == "") &&
    (left == null && right != null ==>
        Repr == {this} + right.Repr &&
        Contents == right.Contents &&
        weight == 0 &&
        data == "") &&
    (left != null && right != null ==>
        Repr == {this} + left.Repr + right.Repr &&
        left.Repr !! right.Repr &&
        Contents == left.Contents + right.Contents &&
        weight == |left.Contents| &&
        data == "") 
}

lemma contentSizeGtZero()
    requires Valid()
    ensures |Contents| > 0
    decreases |Contents|
{
    if left == null && right == null {
        assert data != "";
        assert |Contents| == |data|;
        assert |Contents| > 0;
    } else if left != null && right == null {
        left.contentSizeGtZero();
        assert |Contents| == |left.Contents|;
        assert |Contents| > 0;
    } else if left == null && right != null {
        right.contentSizeGtZero();
        assert |Contents| == |right.Contents|;
        assert |Contents| > 0;
    } else {
        left.contentSizeGtZero();
        right.contentSizeGtZero();
        assert |Contents| == |left.Contents| + |right.Contents|;
        assert |Contents| > 0;
    }
}

function getWeightsOfAllRightChildren(): nat
    reads right, Repr
    requires Valid()
    ensures right != null
        ==> getWeightsOfAllRightChildren() == |right.Contents|
    decreases if right == null then 0 else |right.Contents|
{
    if right == null then 0
    else right.weight + right.getWeightsOfAllRightChildren()
} 

function length(): nat
    reads Repr
    requires Valid()
    ensures |Contents| == length()
    decreases 0
{
    this.weight + getWeightsOfAllRightChildren()
}

// constructor for creating a terminal node
constructor Terminal(x: string)
    requires x != ""
    ensures Valid() && fresh(Repr)
        && left == null && right == null
        && data == x
{ 
    data := x;
    weight := |x|;
    left := null;
    right := null;
    Contents := x;
    Repr := {this};
}   

predicate isTerminal()
    reads this, this.left, this.right
{ left == null && right == null }

method report(i: nat, j: nat) returns (s: string)
    requires 0 <= i <= j <= |this.Contents|
    requires Valid()
    ensures s == this.Contents[i..j]
    decreases if left == null && right == null then 0 else |this.Contents|
{
    if i == j {
        s := "";
    } else {
        if this.left == null && this.right == null {
            s := data[i..j];
        } else {
            if (j <= this.weight) {
                assert left != null;
                var s' := this.left.report(i, j);
                s := s';
            } else if (this.weight <= i) {
                assert right != null;
                var s' := this.right.report(i - this.weight, j - this.weight);
                s := s';
            } else {
                assert left != null && right != null;
                assert i < this.weight && this.weight < j;
                var s1 := this.left.report(i, this.weight);
                var s2 := this.right.report(0, j - this.weight);
                s := s1 + s2;
                assert s == this.Contents[i..j];
            }
        }
    }
}

method toString() returns (s: string)
    requires Valid()
    ensures s == Contents
    decreases 0
{
    s := report(0, this.length());
    assert s == Contents;
}

method getCharAtIndex(index: nat) returns (c: char)
    requires Valid() && 0 <= index < |Contents|
    ensures c == Contents[index]
    decreases |Contents| - index
{
    var nTemp: Rope := this;
    var i := index;
    while (!nTemp.isTerminal()) 
        invariant nTemp != null
        invariant nTemp.Valid()
        invariant 0 <= i < |nTemp.Contents|
        invariant nTemp in nTemp.Repr
        decreases |nTemp.Contents|
    {
        if (i < nTemp.weight) {
            assert nTemp.left != null;
            nTemp := nTemp.left;
        } else {
            assert nTemp.right != null;
            i := i - nTemp.weight;
            nTemp := nTemp.right;
        }
    }
    // Have reached the terminal node with index i
    assert nTemp.isTerminal();
    assert 0 <= i < |nTemp.data|;
    c := nTemp.data[i];
    assert c == Contents[index];
}

static method concat(n1: Rope?, n2: Rope?) returns (n: Rope?) 
    requires (n1 != null) ==> n1.Valid()
    requires (n2 != null) ==> n2.Valid()
    requires (n1 != null && n2 != null) ==> (n1.Repr !! n2.Repr)

    ensures (n1 != null || n2 != null) <==> n != null && n.Valid()
    ensures (n1 == null && n2 == null) <==> n == null
    ensures (n1 == null && n2 != null)
        ==> n == n2 && n != null && n.Valid() && n.Contents == n2.Contents
    ensures (n1 != null && n2 == null)
        ==> n == n1 && n != null && n.Valid() && n.Contents == n1.Contents
    ensures (n1 != null && n2 != null)
        ==> n != null && n.Valid()
            && n.left == n1 && n.right == n2
            && n.Contents == n1.Contents + n2.Contents
            && fresh(n.Repr - n1.Repr - n2.Repr)
    decreases if n1 == null then 0 else if n2 == null then 0 else |n1.Contents| + |n2.Contents|
{
    if (n1 == null) {
        n := n2;
    } else if (n2 == null) {
        n := n1;
    } else {
        n := new Rope.Terminal("placeholder");
        n.left := n1;
        n.right := n2;
        n.data := "";

        var nTemp: Rope := n1;
        var w := 0;
        ghost var nodesTraversed : set<Rope> := {};

        while (nTemp.right != null)
            invariant nTemp != null
            invariant nTemp.Valid()
            invariant nTemp in nTemp.Repr
            invariant w + nTemp.weight + (if nTemp.right != null then |nTemp.right.Contents| else 0) == |n1.Contents|
            invariant w <= |n1.Contents|
            invariant nodesTraversed <= n1.Repr
            decreases |nTemp.Contents|
        {
            w := w + nTemp.weight;
            if (nTemp.left != null) {
                nodesTraversed := nodesTraversed + nTemp.left.Repr + {nTemp};
            } else {
                nodesTraversed := nodesTraversed + {nTemp};
            }
            nTemp := nTemp.right;
        }
        w := w + nTemp.weight;
        if (nTemp.left != null) {
            nodesTraversed := nodesTraversed + nTemp.left.Repr + {nTemp};
        } else {
            nodesTraversed := nodesTraversed + {nTemp};
        }
        n.weight := w;
        n.Contents := n1.Contents + n2.Contents;
        n.Repr := {n} + n1.Repr + n2.Repr;
        assert n.Valid();
        assert n.Contents == n1.Contents + n2.Contents;
        assert fresh(n.Repr - n1.Repr - n2.Repr);
    } 
} 


/**
    Dafny needs help to guess that in our definition, every rope must
    have non-empty Contents, otherwise it is represented by [null].

    The lemma contentSizeGtZero(n) is thus important to prove the
    postcondition of this method, in the two places where the lemma is
    invoked.
*/
static method split(n: Rope, index: nat) returns (n1: Rope?, n2: Rope?) 
    requires n.Valid() && 0 <= index <= |n.Contents|
    ensures index == 0
        ==> n1 == null && n2 != null && n2.Valid()
            && n2.Contents == n.Contents && fresh(n2.Repr - n.Repr)
    ensures index == |n.Contents|
        ==> n2 == null && n1 != null && n1.Valid()
            && n1.Contents == n.Contents && fresh(n1.Repr - n.Repr)
    ensures 0 < index < |n.Contents|
        ==> n1 != null && n1.Valid() && n2 != null && n2.Valid()
            && n1.Contents == n.Contents[..index]
            && n2.Contents == n.Contents[index..]
            && n1.Repr !! n2.Repr
            && fresh(n1.Repr - n.Repr) && fresh(n2.Repr - n.Repr)
    decreases |n.Contents| - index
{
    if (index == 0) {
        n1 := null;
        n2 := n;
        n.contentSizeGtZero();
    } else if (index < n.weight) {
        if (n.left != null) {
            var s1, s2 := split(n.left, index);
            n1 := s1;
            n2 := concat(s2, n.right);
            if n2 != null && s2 != null {
                assert n2.Valid();
                assert n2.Contents == s2.Contents + (if n.right != null then n.right.Contents else "");
            }
        } else {
            // terminal node
            if (index == 0) {
                n1 := null;
                n2 := n;
            } else {
                n1 := new Rope.Terminal(n.data[..index]);
                n2 := new Rope.Terminal(n.data[index..]);
                assert n1.Contents == n.data[..index];
                assert n2.Contents == n.data[index..];
            }
        }
    } else if (index > n.weight) {
        assert n.right != null;
        var s1, s2 := split(n.right, index - n.weight);
        n1 := concat(n.left, s1);
        n2 := s2;
        if n1 != null && n.left != null && s1 != null {
            assert n1.Valid();
            assert n1.Contents == n.left.Contents + s1.Contents;
        }
    } else {
        // since [n.weight == index != 0], it means that [n] cannot be a
        // non-terminal node with [left == null].
        if (n.left != null && n.right == null) {
            n1 := n.left;
            n2 := null;
        } else if (n.left != null && n.right != null) {
            n.right.contentSizeGtZero();
            n1 := n.left;
            n2 := n.right;
        } else {
            n1 := n;
            n2 := null;
        }
    }
}

static method insert(n1: Rope, n2: Rope, index: nat) returns (n: Rope)
    requires n1.Valid() && n2.Valid() && n1.Repr !! n2.Repr
    requires 0 <= index < |n1.Contents|
    ensures n.Valid()
        && n.Contents ==
            n1.Contents[..index] + n2.Contents + n1.Contents[index..]
        && fresh(n.Repr - n1.Repr - n2.Repr)
    decreases |n1.Contents| - index
{
    var n1BeforeIndex, n1AfterIndex := split(n1, index);
    var firstPart := concat(n1BeforeIndex, n2);
    n := concat(firstPart, n1AfterIndex);
    assert n.Valid();
    assert n.Contents == n1.Contents[..index] + n2.Contents + n1.Contents[index..];
}

static method delete(n: Rope, i: nat, j: nat) returns (m: Rope?)
    requires n.Valid()
    requires 0 <= i < j <= |n.Contents|
    ensures (i == 0 && j == |n.Contents|) <==> m == null
    ensures m != null ==>
        m.Valid() &&
        m.Contents == n.Contents[..i] + n.Contents[j..] &&
        fresh(m.Repr - n.Repr)
    decreases |n.Contents| - j
{
    var l1, l2 := split(n, i);
    var r1, r2 := split(l2, j - i);
    m := concat(l1, r2);
    if m != null {
        assert m.Valid();
        assert m.Contents == n.Contents[..i] + n.Contents[j..];
    }
}

static method substring(n: Rope, i: nat, j: nat) returns (m: Rope?)
    requires n.Valid()
    requires 0 <= i < j <= |n.Contents|
    ensures (i == j) <==> m == null
    ensures m != null ==>
        m.Valid() &&
        m.Contents == n.Contents[i..j] &&
        fresh(m.Repr - n.Repr)
    decreases j - i
{
    var l1, l2 := split(n, i);
    var r1, r2 := split(l2, j - i);
    m := r1;
    if m != null {
        assert m.Valid();
        assert m.Contents == n.Contents[i..j];
    }
}

}
// End of Rope Class
}
// End of Rope Module

function abs(a: real) : real {if a>0.0 then a else -a}
