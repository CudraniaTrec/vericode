
// Ch. 8: Sorting

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Length<T>(xs: List<T>): int
  ensures Length(xs) >= 0
{
    match xs
    case Nil => 0
    case Cons(_, tl) => 1 + Length(tl)
}

function At<T>(xs: List, i: nat): T
  requires i < Length(xs)
{
    if i == 0 then xs.head else At(xs.tail, i - 1)
}

ghost predicate Ordered(xs: List<int>) {
    match xs
    case Nil => true
    case Cons(_, Nil) => true
    case Cons(hd0, Cons(hd1, _)) => (hd0 <= hd1) && Ordered(xs.tail)
}

lemma AllOrdered(xs: List<int>, i: nat, j: nat)
  requires Ordered(xs) && i <= j < Length(xs)
  ensures At(xs, i) <= At(xs, j)
{
    if i != 0 {
        assert i > 0;
        assert Length(xs) > 0;
        assert xs is Cons;
        AllOrdered(xs.tail, i - 1, j - 1);
        assert At(xs, i) == At(xs.tail, i - 1);
        assert At(xs, j) == At(xs.tail, j - 1);
    } else if i == j {
        assert At(xs, i) == At(xs, j);
    } else {
        assert i == 0 && j > 0;
        assert xs is Cons;
        assert xs.tail is List<int>;
        assert At(xs, 0) == xs.head;
        assert At(xs, j) == At(xs.tail, j - 1);
        assert xs is Cons;
        assert xs.tail is List<int>;
        assert xs.head <= At(xs.tail, 0);
        AllOrdered(xs.tail, 0, j - 1);
        assert xs.head <= At(xs.tail, j - 1);
    }
}

// Ex. 8.0 generalize fron int to T by: T(==)
ghost function Count<T(==)>(xs: List<T>, p: T): int
  ensures Count(xs, p) >= 0
{
    match xs
    case Nil => 0
    case Cons(hd, tl) => (if hd == p then 1 else 0) + Count(tl, p)
}

ghost function Project<T(==)>(xs: List<T>, p: T): List<T> {
    match xs
    case Nil => Nil
    case Cons(hd, tl) => if hd == p then Cons(hd, Project(tl, p)) else Project(tl, p)
}

// Ex 8.1
lemma {:induction false} CountProject<T(==)>(xs: List<T>, ys: List<T>, p: T)
  requires Project(xs, p) == Project(ys, p)
  ensures Count(xs, p) == Count(ys, p)
{
    match xs
    case Nil => {
        match ys
        case Nil => {}
        case Cons(yhd, ytl) => {
            assert Project(xs, p) == Project(ys, p);
            CountProject(xs, ytl, p);
        }
    }
    case Cons(xhd, xtl) => {
        match ys
        case Nil => {
            assert Project(xs, p) == Project(ys, p);
            CountProject(xtl, ys, p);
        }
        case Cons(yhd, ytl) => {
            if xhd == p && yhd == p {
                assert Project(xs, p) == Cons(xhd, Project(xtl, p));
                assert Project(ys, p) == Cons(yhd, Project(ytl, p));
                assert Project(xtl, p) == Project(ytl, p);
                CountProject(xtl, ytl, p);
            } else if xhd != p && yhd == p {
                assert Project(xs, p) == Project(xtl, p);
                assert Project(ys, p) == Cons(yhd, Project(ytl, p));
                CountProject(xtl, ys, p);
            } else if xhd == p && yhd != p {
                assert Project(xs, p) == Cons(xhd, Project(xtl, p));
                assert Project(ys, p) == Project(ytl, p);
                CountProject(xs, ytl, p);
            } else {
                assert xhd != p && yhd != p;
                assert Project(xs, p) == Project(xtl, p);
                assert Project(ys, p) == Project(ytl, p);
                CountProject(xtl, ytl, p);
            }
        }
    }
}

function InsertionSort(xs: List<int>): List<int>
{
    match xs
    case Nil => Nil
    case Cons(x, rest) => Insert(x, InsertionSort(rest))
}

function Insert(x: int, xs: List<int>): List<int>
{
    match xs
    case Nil => Cons(x, Nil)
    case Cons(hd, tl) => if x < hd then Cons(x, xs) else Cons(hd, Insert(x, tl))
}

lemma InsertionSortOrdered(xs: List<int>)
  ensures Ordered(InsertionSort(xs))
{
    match xs
    case Nil =>
    case Cons(hd, tl) => {
        InsertionSortOrdered(tl);
        assert Ordered(InsertionSort(tl));
        InsertOrdered(hd, InsertionSort(tl));
        assert Ordered(Insert(hd, InsertionSort(tl)));
    }
}

lemma InsertOrdered(y: int, xs: List<int>)
  requires Ordered(xs)
  ensures Ordered(Insert(y, xs))
{
    match xs
    case Nil => {}
    case Cons(hd, tl) => {
        if y < hd {
            assert Ordered(Cons(y, xs));
        } else {
            assert Ordered(xs);
            InsertOrdered(y, tl);
            assert Ordered(Insert(y, tl));
            assert Ordered(Cons(hd, Insert(y, tl)));
        }
    }
}

lemma InsertionSortSameElements(xs: List<int>, p: int)
  ensures Project(xs, p) == Project(InsertionSort(xs), p)
{
    match xs
    case Nil =>
    case Cons(hd, tl) => {
        InsertionSortSameElements(tl, p);
        assert Project(tl, p) == Project(InsertionSort(tl), p);
        InsertSameElements(hd, InsertionSort(tl), p);
        assert Project(Cons(hd, tl), p) == Project(Insert(hd, InsertionSort(tl)), p);
    }
}

lemma InsertSameElements(y: int, xs: List<int>, p: int)
  ensures Project(Cons(y, xs), p) == Project(Insert(y, xs), p)
{
    if xs == Nil {
        assert Insert(y, xs) == Cons(y, Nil);
        assert Project(Cons(y, Nil), p) == (if y == p then Cons(y, Nil) else Nil);
        assert Project(Insert(y, Nil), p) == (if y == p then Cons(y, Nil) else Nil);
    } else {
        match xs
        case Nil => {}
        case Cons(hd, tl) => {
            if y < hd {
                assert Insert(y, xs) == Cons(y, xs);
                assert Project(Cons(y, xs), p) == (if y == p then Cons(y, Project(xs, p)) else Project(xs, p));
                assert Project(Cons(y, xs), p) == Project(Cons(y, xs), p);
            } else {
                assert Insert(y, xs) == Cons(hd, Insert(y, tl));
                InsertSameElements(y, tl, p);
                assert Project(Cons(y, xs), p) == (if y == p then Cons(y, Project(xs, p)) else Project(xs, p));
                assert Project(Cons(hd, Insert(y, tl)), p) == (if hd == p then Cons(hd, Project(Insert(y, tl), p)) else Project(Insert(y, tl), p));
            }
        }
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
