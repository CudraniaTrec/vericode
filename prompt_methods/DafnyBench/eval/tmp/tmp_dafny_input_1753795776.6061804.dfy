
/*
 * Task 2: Define in Dafny the conatural numbers as a coinductive datatype
 * 
 * Being a coinductive data type, it's required that we have a base case constructor and an inductive one 
 * (as is the case with inductive ones as well)
 */
codatatype Conat = Zero | Succ(Pred: Conat)

// Exercise (a): explain why the following coinductive property does NOT hold
// lemma ConstructorConat(n: Conat)
    // ensures n != Succ(n)
// {
    // the following coinductive property does not hold because coinductive datatypes, as opposed to normal datatypes,
    // are designed for infinite domains, as such, it is improper to test the equality above when dealing with infinity
// }

// Exercise (b): show that the constructor successor is injective
greatest lemma ConstructorInjective(x: Conat, y: Conat)
    ensures Succ(x) == Succ(y) ==> x == y
{
    assume Succ(x) == Succ(y);
    // Succ is injective, so their arguments must be equal
    assert Succ(x).Pred == Succ(y).Pred;
    assert x == y;
}

// Exercise (c): define the ∞ constant (as a corecursive function)
// We use a co-recursive call using the Succ constructor on the result, producing an infinite call stack
function inf(n: Conat): Conat
    ensures inf(n) == Succ(inf(n))
{
    Succ(inf(n))
}

// Exercise (d): define the addition of conaturals
// Similar to add function over the Nat datatype (See Lab2)
function add(x: Conat, y: Conat) : Conat
    decreases x
    ensures (x == Zero ==> add(x, y) == y)
    ensures (exists x': Conat :: x == Succ(x') ==> add(x, y) == Succ(add(x.Pred, y)))
{
    match x
        case Zero => y
        case Succ(x') => Succ(add(x', y))
}

// Exercise (e): show that by adding ∞ to itself it remains unchanged
// Because the focus is on greatest fixed-point we need to use a co-predicate
// Aptly renamed to greatest predicate
greatest predicate InfinityAddition()
    ensures add(inf(Zero), inf(Zero)) == inf(Zero)
{
    // Unfold the definition of inf and add:
    // add(inf(Zero), inf(Zero)) == add(Succ(inf(Zero)), inf(Zero)) == Succ(add(inf(Zero), inf(Zero)))
    // inf(Zero) == Succ(inf(Zero))
    assert add(inf(Zero), inf(Zero)) == Succ(add(inf(Zero), inf(Zero)));
    assert inf(Zero) == Succ(inf(Zero));
    // By coinduction, the two are equal
}

// Task 3: Define the parametric streams as a coinductive datatype where s ranges over streams
codatatype Stream<A> = Cons(head: A, tail: Stream<A>)

// Exercise (a): corecursively define the pointwise addition of two streams of integers
// After performing the addition of the value in the heads, proceed similarly with the tails
function addition(a: Stream<int>, b: Stream<int>): Stream<int>
    ensures addition(a, b).head == a.head + b.head
    ensures addition(a, b).tail == addition(a.tail, b.tail)
{ 
    Cons(a.head + b.head, addition(a.tail, b.tail))
}

// Exercise (b): define a parametric integer constant stream
// An infinite stream with the same value
function cnst(a: int): Stream<int>
    ensures cnst(a).head == a
    ensures cnst(a).tail == cnst(a)
{ 
    Cons(a, cnst(a))
}

// Exercise (c): prove by coinduction that add(s, cnst(0)) = s;
// The proof tried below is not complete, however, by telling Dafny that we are dealing with a colemma,
// Aptly renamed to greatest lemma, it is able to reason and prove the post-condition by itself
greatest lemma additionWithZero(a : Stream<int>)
    ensures addition(a, cnst(0)) == a
{
    // Unfold addition and cnst(0):
    // addition(a, cnst(0)) == Cons(a.head + 0, addition(a.tail, cnst(0)))
    // == Cons(a.head, addition(a.tail, cnst(0)))
    // By coinduction, addition(a.tail, cnst(0)) == a.tail
    // So, addition(a, cnst(0)) == Cons(a.head, a.tail) == a
    assert addition(a, cnst(0)).head == a.head;
    assert addition(a, cnst(0)).tail == addition(a.tail, cnst(0));
    assert addition(a, cnst(0)) == Cons(a.head, addition(a.tail, cnst(0)));
    // Coinductive hypothesis applies to a.tail
}

// Exercise (d): define coinductively the predicate
greatest predicate leq(a: Stream<int>, b: Stream<int>)
    decreases a, b
{
    a.head <= b.head && ((a.head == b.head) ==> leq(a.tail, b.tail))
}

// Exercise (e): (e) define the stream blink
function blink(): Stream<int>
    ensures blink().head == 0
    ensures blink().tail.head == 1
    ensures blink().tail.tail == blink()
{
    Cons(0, Cons(1, blink()))
}

// Exercise (f): prove by coinduction that leq(cnst(0), blink)
lemma CnstZeroLeqBlink()
    ensures leq(cnst(0), blink())
{ 
    // Prove leq(cnst(0), blink()) by coinduction
    // cnst(0).head == 0, blink().head == 0, so 0 <= 0
    // Need to show leq(cnst(0).tail, blink().tail), i.e., leq(cnst(0), blink().tail)
    // blink().tail == Cons(1, blink()), so blink().tail.head == 1
    // cnst(0).head == 0 <= 1
    // Now, cnst(0).head != blink().tail.head, so implication is vacuously true
    // Next, leq(cnst(0).tail, blink().tail.tail) == leq(cnst(0), blink())
    // So, the property is preserved coinductively
    // We proceed by coinduction
    var a := cnst(0);
    var b := blink();
    while true
        invariant leq(a, b)
    {
        assert a.head <= b.head;
        if a.head == b.head {
            a := a.tail;
            b := b.tail;
        } else {
            a := a.tail;
            b := b.tail;
        }
    }
}

// Exercise (g): define a function that ”zips” two streams
// A stream formed by alternating the elements of both streams one by one
function zip(a: Stream<int>, b: Stream<int>): Stream<int>
    ensures zip(a, b).head == a.head
    ensures zip(a, b).tail.head == b.head
    ensures zip(a, b).tail.tail == zip(a.tail, b.tail)
{
    Cons(a.head, Cons(b.head, zip(a.tail, b.tail)))
}

// Exercise (h): prove that zipping cnst(0) and cnst(1) yields blink
// By using a greatest lemma, Dafny can reason on its own
greatest lemma ZipCnstZeroCnstOneEqualsBlink()
    ensures zip(cnst(0), cnst(1)) == blink()
{
    // zip(cnst(0), cnst(1)) == Cons(0, Cons(1, zip(cnst(0), cnst(1))))
    // blink() == Cons(0, Cons(1, blink()))
    // By coinduction, zip(cnst(0), cnst(1)) == blink()
    assert zip(cnst(0), cnst(1)).head == blink().head;
    assert zip(cnst(0), cnst(1)).tail.head == blink().tail.head;
    assert zip(cnst(0), cnst(1)).tail.tail == zip(cnst(0).tail, cnst(1).tail);
    assert blink().tail.tail == blink();
    // Coinductive hypothesis applies to zip(cnst(0).tail, cnst(1).tail) == blink()
}

function abs(a: real) : real {if a>0.0 then a else -a}
