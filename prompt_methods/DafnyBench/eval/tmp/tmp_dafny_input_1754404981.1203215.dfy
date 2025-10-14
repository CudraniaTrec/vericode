
datatype Tree = Empty | Node(int,Tree,Tree)

method Main() {
	var tree := BuildBST([-2,8,3,9,2,-7,0]);
	PrintTreeNumbersInorder(tree);
}

method PrintTreeNumbersInorder(t: Tree)
{
	match t {
		case Empty =>
		case Node(n, l, r) =>
			PrintTreeNumbersInorder(l);
			print n;
			print "\n";
			PrintTreeNumbersInorder(r);
	}
}

function NumbersInTree(t: Tree): set<int>
{
	NumbersInSequence(Inorder(t))
}

function NumbersInSequence(q: seq<int>): set<int>
{
	set x | x in q
}

predicate BST(t: Tree)
{
	Ascending(Inorder(t))
}

function Inorder(t: Tree): seq<int>
{
	match t {
		case Empty => []
		case Node(n',nt1,nt2) => Inorder(nt1)+[n']+Inorder(nt2)
	}
}

predicate Ascending(q: seq<int>)
{
	forall i,j :: 0 <= i < j < |q| ==> q[i] < q[j]
}

predicate NoDuplicates(q: seq<int>) { forall i,j :: 0 <= i < j < |q| ==> q[i] != q[j] }

/*
	Goal: Implement correctly, clearly. No need to document the proof obligations.
*/
method BuildBST(q: seq<int>) returns (t: Tree)
	requires NoDuplicates(q)
	ensures BST(t) && NumbersInTree(t) == NumbersInSequence(q)
{
	t := Empty;
	var i: int := 0;
	while i < |q|
		invariant 0 <= i <= |q|
		invariant BST(t)
		invariant NumbersInTree(t) == NumbersInSequence(q[..i])
	{
		t := InsertBST(t, q[i]);
		i := i + 1;
	}
}

/*
	Goal: Implement correctly, efficiently, clearly, documenting the proof obligations
	as we've learned, with assertions and a lemma for each proof goal
*/
method InsertBST(t0: Tree, x: int) returns (t: Tree)
	requires BST(t0) && x !in NumbersInTree(t0)
	ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{x}
{
	match t0 
	{
		case Empty => t := Node(x, Empty, Empty);

		case Node(i, left, right) => 
		{
			if x < i
			{
				LemmaBinarySearchSubtree(i,left,right);
				var newLeft := InsertBST(left, x);
				t := Node(i, newLeft, right);

				// Inorder(t) = Inorder(newLeft) + [i] + Inorder(right)
				// By induction, BST(newLeft) && NumbersInTree(newLeft) == NumbersInTree(left) + {x}
				// BST(right) by LemmaBinarySearchSubtree
				// All elements in Inorder(newLeft) < i, all in Inorder(right) > i
				// Ascending(Inorder(newLeft) + [i] + Inorder(right))
				assert BST(newLeft);
				assert BST(right);
				assert Ascending(Inorder(newLeft));
				assert Ascending(Inorder(right));
				assert forall k :: k in NumbersInSequence(Inorder(newLeft)) ==> k < i;
				assert forall k :: k in NumbersInSequence(Inorder(right)) ==> k > i;
				assert Ascending(Inorder(newLeft) + [i] + Inorder(right));
				assert NumbersInTree(t) == NumbersInTree(left) + NumbersInTree(right) + {i} + {x} - {i}; // {i} already in left/right or not, but x is new
				assert NumbersInTree(t) == NumbersInTree(t0) + {x};
			}
			else
			{
				LemmaBinarySearchSubtree(i,left,right);
				var newRight := InsertBST(right, x);
				t := Node(i, left, newRight);

				// Inorder(t) = Inorder(left) + [i] + Inorder(newRight)
				assert BST(left);
				assert BST(newRight);
				assert Ascending(Inorder(left));
				assert Ascending(Inorder(newRight));
				assert forall k :: k in NumbersInSequence(Inorder(left)) ==> k < i;
				assert forall k :: k in NumbersInSequence(Inorder(newRight)) ==> k > i;
				assert Ascending(Inorder(left) + [i] + Inorder(newRight));
				assert NumbersInTree(t) == NumbersInTree(left) + NumbersInTree(right) + {i} + {x} - {i};
				assert NumbersInTree(t) == NumbersInTree(t0) + {x};
			}
		}
	}
}

lemma	LemmaBinarySearchSubtree(n: int, left: Tree, right: Tree)
	requires BST(Node(n, left, right))
	ensures BST(left) && BST(right)
{
	var qleft, qright := Inorder(left), Inorder(right);
	var q := qleft+[n]+qright;
	LemmaAscendingSubsequence(q, qleft, 0);
	LemmaAscendingSubsequence(q, qright, |qleft|+1);
}

lemma LemmaAscendingSubsequence(q1: seq<int>, q2: seq<int>, i: nat)
	requires i <= |q1|-|q2| && q2 == q1[i..i+|q2|]
	requires Ascending(q1)
	ensures Ascending(q2)
{}

lemma {:verify true} lemma_all_small(q:seq<int>,i:int)
	requires forall k:: k in NumbersInSequence(q) ==> k < i
	requires forall k:: 0 <= k < |q| ==> q[k] in NumbersInSequence(q)
	ensures forall j::0<=j < |q| ==> q[j] < i
{}

lemma {:verify true} lemma_all_big(q:seq<int>,i:int)
	requires forall k:: k in NumbersInSequence(q) ==> k > i
	requires forall k:: 0 <= k < |q| ==> q[k] in NumbersInSequence(q)
	ensures forall j::0<=j < |q| ==> q[j] > i
{}

function abs(a: real) : real {if a>0.0 then a else -a}
