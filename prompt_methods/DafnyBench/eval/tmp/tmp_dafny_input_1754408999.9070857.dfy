
predicate IsOdd(x: int) {
    x % 2 == 1
}

newtype Odd = n : int | IsOdd(n) witness 3

trait OddListSpec
{
    var s: seq<Odd>
    var capacity: nat

    predicate Valid()
        reads this
    {
        0 <= |s| <= this.capacity &&
        forall i :: 0 <= i < |s| ==> IsOdd(s[i] as int)
    }

    method insert(index: nat, element: Odd)
        modifies this
        requires 0 <= index <= |s|
        requires |s| + 1 <= this.capacity
        ensures |s| == |old(s)| + 1
        ensures s[index] == element
        ensures old(capacity) == capacity
        ensures Valid()

    method pushFront(element: Odd)
        modifies this
        requires |s| + 1 <= this.capacity
        ensures |s| == |old(s)| + 1
        ensures s[0] == element
        ensures old(capacity) == capacity
        ensures Valid()

    method pushBack(element: Odd)
        modifies this
        requires |s| + 1 <= this.capacity
        ensures |s| == |old(s)| + 1
        ensures s[|s| - 1] == element
        ensures old(capacity) == capacity
        ensures Valid()

    method remove(element: Odd)
        modifies this
        requires Valid()
        requires |s| > 0
        requires element in s
        ensures |s| == |old(s)| - 1
        ensures old(capacity) == capacity
        ensures Valid()

    method removeAtIndex(index: nat)
        modifies this
        requires Valid()
        requires |s| > 0
        requires 0 <= index < |s|
        ensures |s| == |old(s)| - 1
        ensures old(capacity) == capacity
        ensures Valid()

    method popFront() returns (x: Odd)
        modifies this
        requires Valid()
        requires |s| > 0
        ensures old(s)[0] == x
        ensures |s| == |old(s)| - 1
        ensures old(capacity) == capacity
        ensures Valid()

    method popBack() returns (x: Odd)
        modifies this
        requires Valid()
        requires |s| > 0
        ensures old(s)[|old(s)| - 1] == x
        ensures |s| == |old(s)| - 1
        ensures old(capacity) == capacity
        ensures Valid()

    method length() returns (n: nat)
        ensures n == |s|

    method at(index: nat) returns (x: Odd)
        requires 0 <= index < |s|

    method BinarySearch(element: Odd) returns (index: int)
        requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
        ensures 0 <= index ==> index < |s| && s[index] == element
        ensures index == -1 ==> element !in s[..]

    method mergedWith(l2: OddList) returns (l: OddList)
        requires Valid()
        requires l2.Valid()
        requires this.capacity >= 0 
        requires l2.capacity >= 0 
        requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
        requires forall i, j :: 0 <= i < j < |l2.s| ==> l2.s[i] <= l2.s[j]
        ensures l.capacity == this.capacity + l2.capacity
        ensures |l.s| == |s| + |l2.s|
}

class OddList extends OddListSpec
{
    constructor (capacity: nat)
        ensures Valid()
        ensures |s| == 0
        ensures this.capacity == capacity
    {
        s := [];
        this.capacity := capacity;
    }

    method insert(index: nat, element: Odd)
        modifies this
        requires 0 <= index <= |s|
        requires |s| + 1 <= this.capacity
        ensures |s| == |old(s)| + 1
        ensures s[index] == element
        ensures old(capacity) == capacity
        ensures Valid()
    {
        var tail := s[index..];
        s := s[..index] + [element];
        s := s + tail;
        assert |s| == |old(s)| + 1;
        assert s[index] == element;
        assert old(capacity) == capacity;
        assert Valid();
    }

    method pushFront(element: Odd)
        modifies this
        requires |s| + 1 <= this.capacity
        ensures |s| == |old(s)| + 1
        ensures s[0] == element
        ensures old(capacity) == capacity
        ensures Valid()
    {
        insert(0, element);
        assert |s| == |old(s)| + 1;
        assert s[0] == element;
        assert old(capacity) == capacity;
        assert Valid();
    }

    method pushBack(element: Odd)
        modifies this
        requires |s| + 1 <= this.capacity
        ensures |s| == |old(s)| + 1
        ensures s[|s| - 1] == element
        ensures old(capacity) == capacity
        ensures Valid()
    {
        insert(|s|, element);
        assert |s| == |old(s)| + 1;
        assert s[|s| - 1] == element;
        assert old(capacity) == capacity;
        assert Valid();
    }

    method remove(element: Odd)
        modifies this
        requires Valid()
        requires |s| > 0
        requires element in s
        ensures |s| == |old(s)| - 1
        ensures old(capacity) == capacity
        ensures Valid()
    {
        var found := false;
        var oldS := s;
        var oldCap := capacity;
        var oldLen := |s|;
        var idx: int;
        // Strongest possible invariant:
        // - s is a permutation of oldS except possibly missing one occurrence of element
        // - |s| + (if found then 1 else 0) == oldLen
        // - Valid() holds if found is false (since s is unchanged), or after removal
        // - element in oldS
        // - 0 <= i <= oldLen
        // - if found then s == oldS[..idx] + oldS[idx+1..]
        // - if not found then s == oldS
        //
        // We also want to ensure that after the loop, found is true and s is as required.
        //
        // Invariant:
        //   0 <= i <= oldLen
        //   |s| + (if found then 1 else 0) == oldLen
        //   if found ==> s == oldS[..idx] + oldS[idx+1..]
        //   if !found ==> s == oldS
        //   Valid() holds if !found, and after removal
        //   element in oldS
        //
        var i: int;
        i := 0;
        while i < |s| && !found
            invariant 0 <= i <= oldLen
            invariant |s| + (if found then 1 else 0) == oldLen
            invariant if found then s == oldS[..idx] + oldS[idx+1..] else s == oldS
            invariant Valid() || found
            invariant element in oldS
        {
            if s[i] == element
            {
                idx := i;
                s := s[..i] + s[i + 1..];
                found := true;
                break;
            }
            i := i + 1;
        }
        assert found;
        assert |s| == oldLen - 1;
        assert old(capacity) == capacity;
        assert Valid();
    }

    method removeAtIndex(index: nat)
        modifies this
        requires Valid()
        requires |s| > 0
        requires 0 <= index < |s|
        ensures |s| == |old(s)| - 1
        ensures old(capacity) == capacity
        ensures Valid()
    {
        var oldS := s;
        s := s[..index] + s[index + 1..];
        assert |s| == |oldS| - 1;
        assert old(capacity) == capacity;
        assert Valid();
    }

    method popFront() returns (x: Odd)
        modifies this
        requires Valid()
        requires |s| > 0
        ensures old(s)[0] == x
        ensures |s| == |old(s)| - 1
        ensures old(capacity) == capacity
        ensures Valid() 
    {
        x := s[0];
        var oldS := s;
        s := s[1..];
        assert oldS[0] == x;
        assert |s| == |oldS| - 1;
        assert old(capacity) == capacity;
        assert Valid();
    }

    method popBack() returns (x: Odd)
        modifies this
        requires Valid()
        requires |s| > 0
        ensures old(s)[|old(s)| - 1] == x
        ensures |s| == |old(s)| - 1
        ensures old(capacity) == capacity
        ensures Valid() 
    {
        var oldS := s;
        x := s[|s| - 1];
        s := s[..|s| - 1];
        assert oldS[|oldS| - 1] == x;
        assert |s| == |oldS| - 1;
        assert old(capacity) == capacity;
        assert Valid();
    }

    method length() returns (n: nat)
        ensures n == |s|
    {
        return |s|;
    }

    method at(index: nat) returns (x: Odd)
    requires 0 <= index < |s|
        ensures s[index] == x
    {
        return s[index];
    }

    method BinarySearch(element: Odd) returns (index: int)
        requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
        ensures 0 <= index ==> index < |s| && s[index] == element
        ensures index == -1 ==> element !in s[..]
    {
        var left, right := 0, |s|;

        while left < right
            invariant 0 <= left <= right <= |s|
            invariant forall i :: 0 <= i < left ==> s[i] < element
            invariant forall i :: right <= i < |s| ==> s[i] > element
        {
            var mid := (left + right) / 2;

            if element < s[mid] 
            {
                right := mid;
            } 
            else if s[mid] < element 
            {
                left := mid + 1;
            } 
            else 
            {
                assert s[mid] == element;
                assert 0 <= mid < |s|;
                return mid;
            }
        }

        assert forall i :: 0 <= i < |s| ==> s[i] != element;
        return -1;
    }

    method mergedWith(l2: OddList) returns (l: OddList)
        requires Valid()
        requires l2.Valid()
        requires this.capacity >= 0 
        requires l2.capacity >= 0 
        requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
        requires forall i, j :: 0 <= i < j < |l2.s| ==> l2.s[i] <= l2.s[j]
        ensures l.capacity == this.capacity + l2.capacity
        ensures |l.s| == |s| + |l2.s|
    {
        l := new OddList(this.capacity + l2.capacity);

        var i, j := 0, 0;

        while i < |s| || j < |l2.s|
            invariant 0 <= i <= |s|
            invariant 0 <= j <= |l2.s|
            invariant |l.s| == i + j
            invariant forall k :: 0 <= k < i ==> l.s[k] == s[k]
            invariant forall k :: 0 <= k < j ==> l.s[i + k] == l2.s[k]
            invariant l.capacity == this.capacity + l2.capacity
            invariant l.Valid()
        {
            if i == |s|
            {
                if j == |l2.s|
                {
                    assert |l.s| == |s| + |l2.s|;
                    assert l.capacity == this.capacity + l2.capacity;
                    return l;
                }
                else
                {
                    l.pushBack(l2.s[j]);
                    j := j + 1;
                }
            }
            else
            {
                if j == |l2.s|
                {
                    l.pushBack(s[i]);
                    i := i + 1;
                }
                else
                {
                    if s[i] < l2.s[j]
                    {
                        l.pushBack(s[i]);
                        i := i + 1;
                    } 
                    else
                    {
                        l.pushBack(l2.s[j]);
                        j := j + 1;
                    }
                }
            }
        }
        assert |l.s| == |s| + |l2.s|;
        assert l.capacity == this.capacity + l2.capacity;
        return l;
    }
}

trait CircularLinkedListSpec<T(==)>
{
    var l: seq<T>
    var capacity: nat 

    predicate Valid()
        reads this
    {
        0 <= |l| <= this.capacity
    }

    method insert(index: int, element: T)
    // allows for integer and out-of-bounds index due to circularity
    // managed by applying modulus
        modifies this
        requires |l| + 1 <= this.capacity
        ensures |old(l)| == 0 ==> l == [element]
        ensures |l| == |old(l)| + 1
        ensures |old(l)| > 0 ==> l[index % |old(l)|] == element
        ensures old(capacity) == capacity
        ensures Valid()

    method remove(element: T)
        modifies this
        requires Valid()
        requires |l| > 0
        requires element in l
        ensures |l| == |old(l)| - 1
        ensures old(capacity) == capacity
        ensures Valid()

    method removeAtIndex(index: int)
        modifies this
        requires Valid()
        requires |l| > 0
        ensures |l| == |old(l)| - 1
        ensures old(capacity) == capacity
        ensures Valid()

    method length() returns (n: nat)
        ensures n == |l|

    method at(index: int) returns (x: T)
        requires |l| > 0
        ensures l[index % |l|] == x

    method nextAfter(index: int) returns (x: T)
        requires |l| > 0
        ensures |l| == 1 ==> x == l[0]
        ensures |l| > 1 && index % |l| == (|l| - 1) ==> x == l[0]
        ensures |l| > 1 && 0 <= index && |l| < (|l| - 1) ==> x == l[index % |l| + 1]
}

class CircularLinkedList<T(==)> extends CircularLinkedListSpec<T>
{
    constructor (capacity: nat)
        requires capacity >= 0
        ensures Valid()
        ensures |l| == 0
        ensures this.capacity == capacity
    {
        l := [];
        this.capacity := capacity;
    }

    method insert(index: int, element: T)
    // allows for integer and out-of-bounds index due to circularity
    // managed by applying modulus
        modifies this
        requires |l| + 1 <= this.capacity
        ensures |old(l)| == 0 ==> l == [element]
        ensures |l| == |old(l)| + 1
        ensures |old(l)| > 0 ==> l[index % |old(l)|] == element
        ensures old(capacity) == capacity
        ensures Valid()
    {
        if (|l| == 0)
        {
            l := [element];
        } 
        else 
        {
            var actualIndex := index % |l|;
            var tail := l[actualIndex..];
            l := l[..actualIndex] + [element];
            l := l + tail;
        }
        assert |l| == |old(l)| + 1;
        assert old(capacity) == capacity;
        assert Valid();
    }

    method remove(element: T)
        modifies this
        requires Valid()
        requires |l| > 0
        requires element in l
        ensures |l| == |old(l)| - 1
        ensures old(capacity) == capacity
        ensures Valid()
    {
        var found := false;
        var oldL := l;
        var oldCap := capacity;
        var oldLen := |l|;
        var idx: int;
        var i: int;
        i := 0;
        while i < |l| && !found
            invariant 0 <= i <= oldLen
            invariant |l| + (if found then 1 else 0) == oldLen
            invariant if found then l == oldL[..idx] + oldL[idx+1..] else l == oldL
            invariant Valid() || found
            invariant element in oldL
        {
            if l[i] == element
            {
                idx := i;
                l := l[..i] + l[i + 1..];
                found := true;
                break;
            }
            i := i + 1;
        }
        assert found;
        assert |l| == oldLen - 1;
        assert old(capacity) == capacity;
        assert Valid();
    }

    method removeAtIndex(index: int)
        modifies this
        requires Valid()
        requires |l| > 0
        ensures |l| == |old(l)| - 1
        ensures old(capacity) == capacity
        ensures Valid()
    {
        var oldL := l;
        var actualIndex := index % |l|;
        l := l[..actualIndex] + l[actualIndex + 1..];
        assert |l| == |oldL| - 1;
        assert old(capacity) == capacity;
        assert Valid();
    }

    method length() returns (n: nat)
        ensures n == |l|
    {
        return |l|;
    }

    method at(index: int) returns (x: T)
        requires |l| > 0
        ensures l[index % |l|] == x
    {
        var actualIndex := index % |l|;
        return l[actualIndex];
    }

    method nextAfter(index: int) returns (x: T)
        require
function abs(a: real) : real {if a>0.0 then a else -a}
