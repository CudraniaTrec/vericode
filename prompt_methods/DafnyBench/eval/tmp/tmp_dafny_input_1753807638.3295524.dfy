
// Ch. 10: Datatype Invariants

module PQueue {
    export
        // Impl
        provides PQueue
        provides Empty, IsEmpty, Insert, RemoveMin
        // Spec
        provides Valid, Elements, EmptyCorrect, IsEmptyCorrect
        provides InsertCorrect, RemoveMinCorrect
        reveals IsMin

    // Implementation
    type PQueue = BraunTree
    datatype BraunTree =
        | Leaf
        | Node(x: int, left: BraunTree, right: BraunTree)

    function Empty(): PQueue {
        Leaf
    }

    predicate IsEmpty(pq: PQueue) {
        pq == Leaf
    }

    function Insert(pq: PQueue, y: int): PQueue {
        match pq
        case Leaf => Node(y, Leaf, Leaf)
        case Node(x, left, right) =>
            if y < x then
                Node(y, Insert(right ,x), left)
            else
                Node(x, Insert(right, y), left)
    }

    function RemoveMin(pq: PQueue): (int, PQueue)
      requires Valid(pq) && !IsEmpty(pq)
    {
        var Node(x, left, right) := pq;
        (x, DeleteMin(pq))
    }
    
    function DeleteMin(pq: PQueue): PQueue
      requires IsBalanced(pq) && !IsEmpty(pq)
    {
        if pq.right.Leaf? then
            pq.left
        else if pq.left.x <= pq.right.x then
            Node(pq.left.x, pq.right, DeleteMin(pq.left))
        else
            Node(pq.right.x, ReplaceRoot(pq.right, pq.left.x), DeleteMin(pq.left))
    }

    function ReplaceRoot(pq: PQueue, r: int): PQueue
        requires !IsEmpty(pq)
    {
        if pq.left.Leaf? ||
            (r <= pq.left.x && (pq.right.Leaf? || r <= pq.right.x))
        then
            Node(r, pq.left, pq.right)
        else if pq.right.Leaf? then
            Node(pq.left.x, Node(r, Leaf, Leaf), Leaf)
        else if pq.left.x < pq.right.x then
            Node(pq.left.x, ReplaceRoot(pq.left, r), pq.right)
        else
            Node(pq.right.x, pq.left, ReplaceRoot(pq.right, r))
    }

    //////////////////////////////////////////////////////////////
    // Specification exposed to callers
    //////////////////////////////////////////////////////////////

    ghost function Elements(pq: PQueue): multiset<int> {
        match pq
        case Leaf => multiset{}
        case Node(x, left, right) =>
            multiset{x} + Elements(left) + Elements(right)
    }

    ghost predicate Valid(pq: PQueue) {
        IsBinaryHeap(pq) && IsBalanced(pq)
    }
    
    //////////////////////////////////////////////////////////////
    // Lemmas
    //////////////////////////////////////////////////////////////

    ghost predicate IsBinaryHeap(pq: PQueue) {
        match pq
        case Leaf => true
        case Node(x, left, right) =>
            IsBinaryHeap(left) && IsBinaryHeap(right) &&
            (left.Leaf? || x <= left.x) &&
            (right.Leaf? || x <= right.x)
    }

    ghost predicate IsBalanced(pq: PQueue) {
        match pq
        case Leaf => true
        case Node(_, left, right) =>
            IsBalanced(left) && IsBalanced(right) &&
            var L, R := |Elements(left)|, |Elements(right)|;
            L == R || L == R + 1
    }

    // Ex. 10.2
    lemma {:induction false} BinaryHeapStoresMin(pq: PQueue, y: int)
      requires IsBinaryHeap(pq) && y in Elements(pq)
      ensures pq.x <= y
    {
        if pq.Node? {
            if y == pq.x {
            } else if y in Elements(pq.left) {
                BinaryHeapStoresMin(pq.left, y);
                assert pq.x <= pq.left.x;
                assert pq.left.x <= y;
                assert pq.x <= y;
            } else if y in Elements(pq.right) {
                BinaryHeapStoresMin(pq.right, y);
                assert pq.x <= pq.right.x;
                assert pq.right.x <= y;
                assert pq.x <= y;
            }
        }
    }

    lemma EmptyCorrect()
      ensures Valid(Empty()) && Elements(Empty()) == multiset{}
    {
        assert Empty() == Leaf;
        assert Valid(Leaf);
        assert Elements(Leaf) == multiset{};
    }
    
    lemma IsEmptyCorrect(pq: PQueue)
      requires Valid(pq)
      ensures IsEmpty(pq) <==> Elements(pq) == multiset{}
    {
        if pq == Leaf {
            assert Elements(pq) == multiset{};
        } else {
            assert !IsEmpty(pq);
            assert Elements(pq) != multiset{};
        }
    }
    
    lemma InsertCorrect(pq: PQueue, y: int)
      requires Valid(pq)
      ensures var pq' := Insert(pq, y);
        Valid(pq') && Elements(Insert(pq, y)) == Elements(pq) + multiset{y}
    {
        if pq.Leaf? {
            assert Insert(pq, y) == Node(y, Leaf, Leaf);
            assert Valid(Node(y, Leaf, Leaf));
            assert Elements(Node(y, Leaf, Leaf)) == multiset{y};
            assert Elements(pq) == multiset{};
        } else {
            var x := pq.x;
            var left := pq.left;
            var right := pq.right;
            if y < x {
                InsertCorrect(right, x);
                assert Valid(Insert(right, x));
                assert Valid(Node(y, Insert(right, x), left));
                assert Elements(Insert(right, x)) == Elements(right) + multiset{x};
                assert Elements(Node(y, Insert(right, x), left)) == multiset{y} + Elements(Insert(right, x)) + Elements(left);
                assert Elements(Node(y, Insert(right, x), left)) == multiset{y} + Elements(right) + multiset{x} + Elements(left);
                assert Elements(Node(x, left, right)) == multiset{x} + Elements(left) + Elements(right);
                assert Elements(Insert(pq, y)) == multiset{y} + Elements(pq);
            } else {
                InsertCorrect(right, y);
                assert Valid(Insert(right, y));
                assert Valid(Node(x, Insert(right, y), left));
                assert Elements(Insert(right, y)) == Elements(right) + multiset{y};
                assert Elements(Node(x, Insert(right, y), left)) == multiset{x} + Elements(Insert(right, y)) + Elements(left);
                assert Elements(Node(x, Insert(right, y), left)) == multiset{x} + Elements(right) + multiset{y} + Elements(left);
                assert Elements(Node(x, left, right)) == multiset{x} + Elements(left) + Elements(right);
                assert Elements(Insert(pq, y)) == Elements(pq) + multiset{y};
            }
        }
    }

    lemma RemoveMinCorrect(pq: PQueue)
      requires Valid(pq)
      requires !IsEmpty(pq)
      ensures var (y, pq') := RemoveMin(pq);
              Elements(pq) == Elements(pq') + multiset{y} &&
              IsMin(y, Elements(pq)) &&
              Valid(pq')
    {
        DeleteMinCorrect(pq);
        var Node(x, left, right) := pq;
        var pq' := DeleteMin(pq);
        assert Elements(pq) == Elements(pq') + multiset{x};
        assert IsMin(x, Elements(pq));
        assert Valid(pq');
    }
    
    lemma {:induction false} {:rlimit 1000} {:vcs_split_on_every_assert} DeleteMinCorrect(pq: PQueue)
      requires Valid(pq) && !IsEmpty(pq)
      ensures var pq' := DeleteMin(pq);
        Valid(pq') &&
        Elements(pq') + multiset{pq.x} == Elements(pq) &&
        |Elements(pq')| == |Elements(pq)| - 1
    {
        if pq.right.Leaf? {
            // pq = Node(x, left, Leaf)
            assert DeleteMin(pq) == pq.left;
            assert Elements(DeleteMin(pq)) + multiset{pq.x} == Elements(pq.left) + multiset{pq.x};
            assert Elements(pq) == multiset{pq.x} + Elements(pq.left) + Elements(pq.right);
            assert pq.right == Leaf;
            assert Elements(pq.right) == multiset{};
            assert Elements(pq) == multiset{pq.x} + Elements(pq.left);
            assert Elements(DeleteMin(pq)) + multiset{pq.x} == Elements(pq);
            assert |Elements(DeleteMin(pq))| == |Elements(pq.left)|;
            assert |Elements(pq)| == 1 + |Elements(pq.left)|;
            assert |Elements(DeleteMin(pq))| == |Elements(pq)| - 1;
            assert Valid(DeleteMin(pq));
        }
        else if pq.left.x <= pq.right.x {
            DeleteMinCorrect(pq.left);
            assert Valid(DeleteMin(pq.left));
            assert Valid(Node(pq.left.x, pq.right, DeleteMin(pq.left)));
            assert Elements(Node(pq.left.x, pq.right, DeleteMin(pq.left))) + multiset{pq.x}
                == multiset{pq.left.x} + Elements(pq.right) + Elements(DeleteMin(pq.left)) + multiset{pq.x};
            assert Elements(pq) == multiset{pq.x} + Elements(pq.left) + Elements(pq.right);
            assert Elements(pq.left) == multiset{pq.left.x} + Elements(DeleteMin(pq.left));
            assert Elements(Node(pq.left.x, pq.right, DeleteMin(pq.left))) + multiset{pq.x}
                == multiset{pq.left.x} + Elements(pq.right) + Elements(DeleteMin(pq.left)) + multiset{pq.x};
            assert Elements(pq) == multiset{pq.x} + multiset{pq.left.x} + Elements(DeleteMin(pq.left)) + Elements(pq.right);
            assert Elements(Node(pq.left.x, pq.right, DeleteMin(pq.left))) + multiset{pq.x} == Elements(pq);
            assert |Elements(DeleteMin(pq.left))| == |Elements(pq.left)| - 1;
            assert |Elements(Node(pq.left.x, pq.right, DeleteMin(pq.left)))| == 1 + |Elements(pq.right)| + |Elements(DeleteMin(pq.left))|;
            assert |Elements(pq)| == 1 + |Elements(pq.left)| + |Elements(pq.right)|;
            assert |Elements(Node(pq.left.x, pq.right, DeleteMin(pq.left)))| == |Elements(pq)| - 1;
        } else {
            var left := ReplaceRoot(pq.right, pq.left.x);
            var right := DeleteMin(pq.left);
            var pqp := Node(pq.right.x, left, right);

            ReplaceRootCorrect(pq.right, pq.left.x);
            DeleteMinCorrect(pq.left);

            calc {
                Elements(pqp) + multiset{pq.x};
            ==  // defn Elements
                (multiset{pq.right.x} + Elements(left) + Elements(right)) + multiset{pq.x};
            ==  // multiset left assoc
                ((multiset{pq.right.x} + Elements(left)) + Elements(right)) + multiset{pq.x};
            == { }
                ((Elements(pq.right) + multiset{pq.left.x}) + Elements(right)) + multiset{pq.x};
            ==  // defn right
                ((Elements(pq.right) + multiset{pq.left.x}) + Elements(DeleteMin(pq.left))) + multiset{pq.x};
            ==  // multiset right assoc
                (Elements(pq.right) + (multiset{pq.left.x} + Elements(DeleteMin(pq.left)))) + multiset{pq.x};
            == { }
                (Elements(pq.right) + (Elements(pq.left))) + multiset{pq.x};
            ==
                multiset{pq.x} + Elements(pq.right) + Elements(pq.left);
            ==
                Elements(pq);
            }
            assert Valid(pqp);
            assert |Elements(pqp)| == |Elements(pq)| - 1;
        }
    }

    lemma {:induction false} {:rlimit 1000} {:vcs_split_on_every_assert} ReplaceRootCorrect(pq: PQueue, r: int)
      requires Valid(pq) && !IsEmpty(pq)
      ensures var pq' := ReplaceRoot(pq, r);
        Valid(pq') &&
        r in Elements(pq') &&
        |Elements(pq')| == |Elements(pq)| &&
        Elements(pq) + multiset{r} == Elements(pq') + multiset{pq.x}
    {
        var pq' := ReplaceRoot(pq, r);
        if pq.left.Leaf? ||
            (r <= pq.left.x && (pq.right.Leaf? || r <= pq.right.x))
        {
            assert pq'.x == r;
            assert pq'.left == pq.left;
            assert pq'.right == pq.right;
            assert Elements(pq') == multiset{r} + Elements(pq.left) + Elements(pq.right);
            assert Elements(pq) == multiset{pq.x} + Elements(pq.left) + Elements(pq.right);
            assert Elements(pq) + multiset{r} == Elements(pq') + multiset{pq.x};
            assert |Elements(pq')| == |Elements(pq)|;
            assert r in Elements(pq');
            assert Valid(pq');
        }
        else if pq.right.Leaf? {
            assert pq.left.Node?;
            assert pq.right == Leaf;
            assert pq'.x == pq.left.x;
            assert pq'.left.x == r;
            assert pq'.left.left == Leaf;
            assert pq'.left.right == Leaf;
            assert pq'.right == Leaf;
            assert Elements(pq') == multiset{pq.left.x} + multiset{r};
            assert Elements(pq) == multiset{pq.x} + multiset{pq.left.x};
            assert Elements(pq) + multiset{r} == Elements(pq') + multiset{pq.x};
            assert |Elements(pq')| == |Elements(pq)|;
            assert r in Elements(pq');
            assert Valid(pq');
        }
        else if pq.left.x < pq.right.x {
            ReplaceRootCorrect(pq.left, r);
            assert |Elements(ReplaceRoot(pq.left, r))| == |Elements(pq.left)|;
            assert r in Elements(ReplaceRoot(pq.left, r));
            assert |Elements(pq')| == |Elements(pq)|;
            assert r in Elements(pq');
            assert Valid(pq');
        }
        else {
            ReplaceRootCorrect(pq.right, r);
            assert |Elements(ReplaceRoot(pq.right, r))| == |Elements(pq.right)|;
            assert r in Elements(ReplaceRoot(pq.right, r));
            assert |Elements(pq')| == |Elements(pq)|;
            assert r in Elements(pq');
            assert Valid(pq');
        }
    }

    ghost predicate IsMin(y: int, s: multiset<int>) {
        y in s && forall x :: x in s ==> y <= x
    }

}

// Ex 10.0, 10.1
module PQueueClient {
    import PQ = PQueue

    method Client() {
        var pq := PQ.Empty();
        PQ.EmptyCorrect();
        PQ.InsertCorrect(pq, 1);
        var pq1 := PQ.Insert(pq, 1);

        PQ.InsertCorrect(pq1, 2);
        var pq2 := PQ.Insert(pq1, 2);

        PQ.IsEmptyCorrect(pq2);
        PQ.RemoveMinCorrect(pq2);
        var (m, pq3) := PQ.RemoveMin(pq2);        

        PQ.IsEmptyCorrect(pq3);
        PQ.RemoveMinCorrect(pq3);
        var (n, pq4) := PQ.RemoveMin(pq3);        

        PQ.IsEmptyCorrect(pq4);

    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
