
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
		t := InsertBST(t,q[i]);
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
			var tmp:Tree:= Empty;
			if x < i
			{
				LemmaBinarySearchSubtree(i,left,right);
				tmp :=  InsertBST(left, x);
				t := Node(i, tmp, right);

				ghost var right_nums := Inorder(right);
				ghost var left_nums := Inorder(left);
				ghost var all_nums := Inorder(t0);
				ghost var new_all_nums := Inorder(t);
				ghost var new_left_nums := Inorder(tmp);

				// Inorder(t) = Inorder(tmp) + [i] + Inorder(right)
				assert new_all_nums == new_left_nums + [i] + right_nums;
				// NumbersInTree(t) = NumbersInTree(tmp) + {i} + NumbersInTree(right)
				assert NumbersInTree(t) == NumbersInTree(tmp) + {i} + NumbersInTree(right);
				// By induction, BST(tmp) && NumbersInTree(tmp) == NumbersInTree(left) + {x}
				assert BST(tmp);
				assert NumbersInTree(tmp) == NumbersInTree(left) + {x};
				// BST(right) by LemmaBinarySearchSubtree
				assert BST(right);
				// BST(t) = Ascending(Inorder(t))
				// Inorder(t) = Inorder(tmp) + [i] + Inorder(right)
				// Inorder(tmp) = Inorder(left) with x inserted, and x < i
				// All elements in Inorder(tmp) < i
				assert forall k :: k in NumbersInSequence(new_left_nums) ==> k < i;
				lemma_all_small(new_left_nums, i);
				// All elements in right_nums > i
				assert forall k :: k in NumbersInSequence(right_nums) ==> k > i;
				lemma_all_big(right_nums, i);
				// Ascending(new_left_nums + [i] + right_nums)
				assert Ascending(new_left_nums + [i] + right_nums);
				assert BST(t);
				// NumbersInTree(t) == NumbersInTree(t0) + {x}
				assert NumbersInTree(t) == NumbersInTree(t0) + {x};
			}
			else
			{
				LemmaBinarySearchSubtree(i,left,right);
				tmp := InsertBST(right, x);
				t := Node(i, left, tmp);

				ghost var right_nums := Inorder(right);
				ghost var left_nums := Inorder(left);
				ghost var all_nums := Inorder(t0);
				ghost var new_all_nums := Inorder(t);
				ghost var new_right_nums := Inorder(tmp);

				// Inorder(t) = Inorder(left) + [i] + Inorder(tmp)
				assert new_all_nums == left_nums + [i] + new_right_nums;
				// NumbersInTree(t) = NumbersInTree(left) + {i} + NumbersInTree(tmp)
				assert NumbersInTree(t) == NumbersInTree(left) + {i} + NumbersInTree(tmp);
				// By induction, BST(tmp) && NumbersInTree(tmp) == NumbersInTree(right) + {x}
				assert BST(tmp);
				assert NumbersInTree(tmp) == NumbersInTree(right) + {x};
				// BST(left) by LemmaBinarySearchSubtree
				assert BST(left);
				// All elements in left_nums < i
				assert forall k :: k in NumbersInSequence(left_nums) ==> k < i;
				lemma_all_small(left_nums, i);
				// All elements in new_right_nums > i
				assert forall k :: k in NumbersInSequence(new_right_nums) ==> k > i;
				lemma_all_big(new_right_nums, i);
				// Ascending(left_nums + [i] + new_right_nums)
				assert Ascending(left_nums + [i] + new_right_nums);
				assert BST(t);
				// NumbersInTree(t) == NumbersInTree(t0) + {x}
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
	// By definition of BST, Ascending(q)
	// Subsequence of ascending sequence is ascending
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
