
/*
 * Task 2: Define the natural numbers as an algebraic data type
 * 
 * Being an inductive data type, it's required that we have a base case constructor and an inductive one.
 */
datatype Nat = Zero | S(Pred: Nat)

/// Task 2
// Exercise (a'): proving that the successor constructor is injective
/*
 * It's known that the successors are equal.
 * It's know that for equal inputs, a non-random function returns the same result.
 * Thus, the predecessors of the successors, namely, the numbers themselves, are equal.
 */
lemma SIsInjective(x: Nat, y: Nat)
    ensures S(x) == S(y) ==> x == y
{
    assume S(x) == S(y);
    // S(x) == S(y) iff x == y by definition of datatype equality
    assert x == y;
}

// Exercise (a''): Zero is different from successor(x), for any x
/*
 * For all x: Nat, S(x) is built using the S constructor, implying that S(x).Zero? is inherently false.
 */
lemma ZeroIsDifferentFromSuccessor(n: Nat)
    ensures S(n) != Zero
{
    // By definition of datatype, S(n) != Zero
    assert S(n) != Zero;
}

// Exercise (b): inductively defining the addition of natural numbers
/*
 * The function decreases y until it reaches the base inductive case.
 * The Addition between Zero and a x: Nat will be x.
 * The Addition between a successor of a y': Nat and another x: Nat is the successor of the Addition between y' and x
 *
 * x + y = 1 + ((x - 1) + y)
 */
function Add(x: Nat, y: Nat) : Nat
{
    match y
        case Zero => x
        case S(y') => S(Add(x, y')) 
}

// Exercise (c'): proving that the addition is commutative
/*
 * It is necessary, as with any induction, to have a proven base case.
 * In this case, we first prove that the Addition with Zero is Neutral.
 */
 lemma {:induction n} ZeroAddNeutral(n: Nat)
    ensures Add(n, Zero) == Add(Zero, n) == n
{
    match n
        case Zero => {
            // Add(Zero, Zero) == Zero
            assert Add(Zero, Zero) == Zero;
            assert Add(Zero, n) == n;
            assert n == Zero;
        }
        case S(n') => {
            // Add(S(n'), Zero) == S(n')
            assert Add(S(n'), Zero) == S(n');
            // Add(Zero, S(n')) == S(Add(Zero, n'))
            assert Add(Zero, S(n')) == S(Add(Zero, n'));
            // Inductive hypothesis: Add(Zero, n') == n'
            ZeroAddNeutral(n');
            assert Add(Zero, n') == n';
            assert Add(Zero, S(n')) == S(n');
            assert Add(Zero, n) == n;
        }
}

/*
 * Since Zero is neutral, it is trivial that the order of addition is not of importance.
 */
lemma {:induction n} ZeroAddCommutative(n: Nat)
    ensures Add(Zero, n) == Add(n, Zero)
{
    ZeroAddNeutral(n);
    assert Add(Zero, n) == n;
    assert Add(n, Zero) == n;
}

/*
 * Since now the base case of commutative addition with Zero is proven, we can now prove using induction.
 */
lemma {:induction x, y} AddCommutative(x: Nat, y: Nat)
    ensures Add(x, y) == Add(y, x)
{
    match x
        case Zero => ZeroAddCommutative(y);
        case S(x') => {
            AddCommutative(x', y);
            // Add(S(x'), y) == S(Add(x', y))
            assert Add(S(x'), y) == S(Add(x', y));
            // Add(y, S(x')) == S(Add(y, x'))
            assert Add(y, S(x')) == S(Add(y, x'));
            AddCommutative(y, x');
            assert Add(x', y) == Add(y, x');
            assert S(Add(x', y)) == S(Add(y, x'));
            assert Add(S(x'), y) == Add(y, S(x'));
        }
}

// Exercise (c''): proving that the addition is associative
/*
 * It is necessary, as with any induction, to have a proven base case.
 * In this case, we first prove that the Addition with Zero is Associative.
 *
 * Again, given that addition with Zero is neutral, the order of calculations is irrelevant.
 */
lemma {:induction x, y} ZeroAddAssociative(x: Nat, y: Nat)
    ensures Add(Add(Zero, x), y) == Add(Zero, Add(x, y))
{
    ZeroAddNeutral(x);
    // Add(Zero, x) == x
    assert Add(Zero, x) == x;
    // Add(x, y) == Add(Zero, Add(x, y)) by ZeroAddNeutral
    assert Add(Add(Zero, x), y) == Add(x, y);
    assert Add(Zero, Add(x, y)) == Add(x, y);
}

/*
 * Since now the base case of commutative addition with Zero is proven, we can now prove using induction.
 */
lemma {:induction x, y, z} AddAssociative(x: Nat, y: Nat, z: Nat)
    ensures Add(Add(x, y), z) == Add(x, Add(y, z))
{
    match z
        case Zero => {
            ZeroAddAssociative(Add(x, y), Zero);
            assert Add(Add(x, y), Zero) == Add(x, y);
            assert Add(x, Add(y, Zero)) == Add(x, y);
        }
        case S(z') => {
            AddAssociative(x, y, z');
            // Add(Add(x, y), S(z')) == S(Add(Add(x, y), z'))
            assert Add(Add(x, y), S(z')) == S(Add(Add(x, y), z'));
            // Add(x, Add(y, S(z'))) == Add(x, S(Add(y, z'))) == S(Add(x, Add(y, z')))
            assert Add(x, Add(y, S(z'))) == S(Add(x, Add(y, z')));
            assert S(Add(Add(x, y), z')) == S(Add(x, Add(y, z')));
            assert Add(Add(x, y), S(z')) == Add(x, Add(y, S(z')));
        }
}

// Exercise (d): defining a predicate lt(m, n) that holds when m is less than n
/*
 * If x is Zero and y is a Successor, given that we have proven ZeroIsDifferentFromSuccessor for all x, the predicate holds.
 * Otherwise, if both are successors, we inductively check their predecessors.
 */
predicate LessThan(x: Nat, y: Nat)
{
    (x.Zero? && y.S?) || (x.S? && y.S? && LessThan(x.Pred, y.Pred))
}

// Exercise (e): proving that lt is transitive
/*
 * It is necessary, as with any induction, to have a proven base case.
 * In this case, we first prove that LessThan is Transitive having a Zero as the left-most parameter.
 *
 * We prove this statement using Reductio Ad Absurdum.
 * We suppose that Zero is not smaller that an arbitrary z that is non-Zero.
 * This would imply that Zero has to be a Successor (i.e. Zero.S? == true).
 * This is inherently false.
 */
lemma {:induction y, z} LessThanIsTransitiveWithZero(y: Nat, z: Nat)
    requires LessThan(Zero, y)
    requires LessThan(y, z)
    ensures LessThan(Zero, z)
{
    // LessThan(Zero, y) => y.S?
    assert y.S?;
    // LessThan(y, z) => z.S? or (y.S? && z.S? && LessThan(y.Pred, z.Pred))
    if !LessThan(Zero, z) {
        // Then z is Zero or z is S(z') but not LessThan(Zero, z)
        if z.Zero? {
            // But LessThan(y, z) requires y.Zero? && z.S? or y.S? && z.S? && LessThan(y.Pred, z.Pred)
            // But z.Zero? so LessThan(y, z) cannot hold
            assert false;
        }
    }
    assert LessThan(Zero, z);
}

/*
 * Since now the base case of transitive LessThan with Zero is proven, we can now prove using induction.
 *
 * In this case, the induction decreases on all three variables, all x, y, z until the base case.
 */
lemma {:induction x, y, z} LessThanIsTransitive(x: Nat, y: Nat, z: Nat)
    requires LessThan(x, y)
    requires LessThan(y, z)
    ensures LessThan(x, z)
    decreases x, y, z
{
    match x
        case Zero => {
            LessThanIsTransitiveWithZero(y, z);
            assert LessThan(Zero, z);
        }
        case S(x') => match y
                          case S(y') => match z    
                                            case S(z') => {
                                                LessThanIsTransitive(x', y', z');
                                                assert LessThan(x', y');
                                                assert LessThan(y', z');
                                                assert LessThan(x', z');
                                                assert LessThan(S(x'), S(z'));
                                            }
}

// Task 3: Define the parametric lists as an algebraic data type
/*
 * Being an inductive data type, it's required that we have a base case constructor and an inductive one.
 * The inductive Append constructor takes as input a Nat, the head, and a tail, the rest of the list.
 */
datatype List<T> = Nil | Append(head: T, tail: List)

// Exercise (a): defining the size of a list (using natural numbers defined above)
/*
 * We are modelling the function as a recursive one.
 * The size of an empty list (Nil) is Zero.
 * 
 * The size of a non-empty list is the successor of the size of the list's tail.
 */
function Size(l: List<Nat>): Nat
{
    if l.Nil? then Zero else S(Size(l.tail))
}

// Exercise (b): defining the concatenation of two lists
/*
 * Concatenation with an empty list yields the other list.
 * 
 * The function recursively calculates the result of the concatenation.
 */
function Concatenation(l1: List<Nat>, l2: List<Nat>) : List<Nat>
{
    match l1
        case Nil => l2
        case Append(head1, tail1) => match l2
                                         case Nil => l1
                                         case Append(_, _) => Append(head1, Concatenation(tail1, l2))
}

// Exercise (c): proving that the size of the concatenation of two lists is the sum of the lists' sizes
/*
 * Starting with a base case in which the first list is empty, the proof is trivial, given ZeroAddNeutral.
 * Afterwards, the induction follows the next step and matches the second list.
 * If the list is empty, the result will be, of course, the first list.
 * Otherwise, an element is discarded from both (the heads), and the verification continues on the tails.
 */
lemma {:induction l1, l2} SizeOfConcatenationIsSumOfSizes(l1: List<Nat>, l2: List<Nat>)
    ensures Size(Concatenation(l1, l2)) == Add(Size(l1), Size(l2))
{
    match l1
        case Nil => {
            ZeroAddNeutral(Size(l2));
            assert Size(Concatenation(Nil, l2)) == Size(l2);
            assert Add(Zero, Size(l2)) == Size(l2);
            assert Add(Size(l1), Size(l2)) == Size(l2);
        }
        case Append(_, tail1) => match l2
                                     case Nil => {
                                        assert Concatenation(l1, Nil) == l1;
                                        assert Size(Concatenation(l1, Nil)) == Size(l1);
                                        assert Add(Size(l1), Zero) == Size(l1);
                                        assert Add(Size(l1), Size(l2)) == Size(l1);
                                     }
                                     case Append(_, tail2) => {
                                        SizeOfConcatenationIsSumOfSizes(tail1, l2);
                                        assert Size(Concatenation(tail1, l2)) == Add(Size(tail1), Size(l2));
                                        assert Size(Concatenation(l1, l2)) == S(Size(Concatenation(tail1, l2)));
                                        assert Add(Size(l1), Size(l2)) == S(Add(Size(tail1), Size(l2)));
                                        assert Size(Concatenation(l1, l2)) == Add(Size(l1), Size(l2));
                                     }
}

// Exercise (d): defining a function reversing a list
/*
 * The base case is, again, the empty list. 
 * When the list is empty, the reverse of the list is also Nil.
 * 
 * When dealing with a non-empty list, we make use of the Concatenation operation.
 * The Reverse of the list will be a concatenation between the reverse of the tail and the head.
 * Since the head is not a list on its own, a list is created using the Append constructor.
 */
function ReverseList(l: List<Nat>) : List<Nat>
{
    if l.Nil? then Nil else Concatenation(ReverseList(l.tail), Append(l.head, Nil))
}

// Exercise (e): proving that reversing a list twice we obtain the initial list.
/*
 * Given that during the induction we need to make use of this property, 
 * we first save the result of reversing a concatenation between a list and a single element.
 *
 * Aside from the base case, proven with chained equality assertions, the proof follows an inductive approach as well.
 */
lemma {:induction l, n} ReversalOfConcatenationWithHead(l: List<Nat>, n: Nat)
    ensures ReverseList(Concatenation(l, Append(n, Nil))) == Append(n, ReverseList(l))
{
    match l
        case Nil => {
            assert Concatenation(Nil, Append(n, Nil)) == Append(n, Nil);
            assert ReverseList(Append(n, Nil)) == Concatenation(ReverseList(Nil), Append(n, Nil));
            assert ReverseList(Append(n, Nil)) == Append(n, Nil);
            assert Append(n, Nil) == Append(n, ReverseList(Nil));
        }
        case Append(head, tail) => {
            ReversalOfConcatenationWithHead(tail, n);
            assert Concatenation(Append(head, tail), Append(n, Nil)) == Append(head, Concatenation(tail, Append(n, Nil)));
            assert ReverseList(Append(head, Concatenation(tail, Append(n, Nil)))) == Concatenation(ReverseList(Concatenation(tail, Append(n, Nil))), Append(head, Nil));
            assert ReverseList(Concatenation(l, Append(n, Nil))) == Concatenation(ReverseList(Concatenation(tail, Append(n, Nil))), Append(head, Nil));
            assert ReverseList(Concatenation(l, Append(n, Nil))) == Append(n, ReverseList(l));
        }
}

/*
 * The induction starts with the base case, which is trivial.
 *
 * For the inductive steps, there is a need for the property proven above.
 * Once the property is guaranteed, the chained assertions lead to the solution.
 */
lemma {:induction l} DoubleReversalResultsInInitialList(l: List<Nat>)
    ensures l == ReverseList(ReverseList(l))
{
    match l
        case Nil => {
            assert ReverseList(ReverseList(Nil)) == ReverseList(Nil);
            assert ReverseList(Nil) == Nil;
        }
        case Append(head, tail) => {
            ReversalOfConcatenationWithHead(ReverseList(tail), head);
            DoubleReversalResultsInInitialList(tail);
            assert ReverseList(ReverseList(Append(head, tail))) == ReverseList(Concatenation(ReverseList(tail), Append(head, Nil)));
            assert ReverseList(Concatenation(ReverseList(tail), Append(head, Nil))) == Append(head, ReverseList(ReverseList(tail)));
            assert ReverseList(ReverseList(tail)) == tail;
            assert Append(head, tail) == l;
        }
}

function abs(a: real) : real {if a>0.0 then a else -a}
