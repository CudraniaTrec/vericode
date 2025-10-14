
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
		invariant NoDuplicates(q)
	{
		assert i < |q| ==> q[i] !in NumbersInTree(t); // Because NoDuplicates(q)
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
			var tmp:Tree;
			if x < i
			{
				LemmaBinarySearchSubtree(i,left,right);
				tmp :=  InsertBST(left, x);
				t := Node(i, tmp, right);

				// Inorder(t) = Inorder(tmp) + [i] + Inorder(right)
				// BST(tmp) and BST(right) and all in tmp < i, all in right > i
				// Ascending(Inorder(tmp) + [i] + Inorder(right))
				// NumbersInTree(t) = NumbersInTree(tmp) + {i} + NumbersInTree(right)
				// NumbersInTree(tmp) = NumbersInTree(left) + {x}
				// So NumbersInTree(t) = NumbersInTree(left) + {x} + {i} + NumbersInTree(right)
				// = NumbersInTree(t0) + {x}
			}
			else
			{
				LemmaBinarySearchSubtree(i,left,right);
				tmp := InsertBST(right, x);
				t := Node(i, left, tmp);

				// Inorder(t) = Inorder(left) + [i] + Inorder(tmp)
				// BST(left) and BST(tmp) and all in left < i, all in tmp > i
				// Ascending(Inorder(left) + [i] + Inorder(tmp))
				// NumbersInTree(t) = NumbersInTree(left) + {i} + NumbersInTree(tmp)
				// NumbersInTree(tmp) = NumbersInTree(right) + {x}
				// So NumbersInTree(t) = NumbersInTree(left) + {i} + NumbersInTree(right) + {x}
				// = NumbersInTree(t0) + {x}
			}
		}
	}
}

lemma	LemmaBinarySearchSubtree(n: int, left: Tree, right: Tree)
	requires BST(Node(n, left, right))
	ensures BST(left) && BST(right)
{
	// BST(Node(n, left, right)) means Ascending(Inorder(left) + [n] + Inorder(right))
	// So Ascending(Inorder(left)) and Ascending(Inorder(right))
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
