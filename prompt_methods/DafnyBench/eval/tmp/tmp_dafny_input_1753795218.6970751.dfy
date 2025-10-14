
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
        assert Valid();
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
        assert s[0] == element;
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
        assert s[|s| - 1] == element;
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
        var oldLen := |s|;
        var oldCap := capacity;
        var oldElement := element;
        var oldValid := Valid();
        var oldCount := (function (a: seq<Odd>, e: Odd): nat { |set i | 0 <= i < |a| && a[i] == e| })(oldS, oldElement);
        var oldSSeq := s;
        var oldCapSeq := capacity;
        var oldValidSeq := Valid();
        var oldLenSeq := |s|;
        var oldElementSeq := element;
        var oldCountSeq := (function (a: seq<Odd>, e: Odd): nat { |set i | 0 <= i < |a| && a[i] == e| })(oldSSeq, oldElementSeq);

        var i: int := 0;
        while i < |s|
            invariant 0 <= i <= |s|
            invariant |s| + (|old(s)| - i) == |old(s)|
            invariant Valid()
            decreases |s| - i
        {
            if s[i] == element
            {
                s := s[..i] + s[i + 1..];
                found := true;
                break;
            }
            i := i + 1;
        }
        assert found;
        assert |s| == |oldS| - 1;
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
        s := s[..index] + s[index + 1..];
        assert |s| == |old(s)| - 1;
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
        s := s[1..];
        assert old(s)[0] == x;
        assert |s| == |old(s)| - 1;
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
        x := s[|s| - 1];
        s := s[..|s| - 1];
        assert old(s)[|old(s)| - 1] == x;
        assert |s| == |old(s)| - 1;
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
            invariant forall i :: right <= i < |s| ==> element < s[i]
            decreases right - left
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
                assert mid < |s|;
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
            decreases |s| + |l2.s| - (i + j)
        {
            if i == |s|
            {
                if j == |l2.s|
                {
                    assert |l.s| == |s| + |l2.s|;
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
        assert Valid();
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
            assert l == [element];
        } 
        else 
        {
            var actualIndex := index % |l|;
            var tail := l[actualIndex..];
            l := l[..actualIndex] + [element];
            l := l + tail;
            assert l[actualIndex] == element;
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
        var i: nat := 0;
        while i < |l|
            invariant 0 <= i <= |l|
            invariant Valid()
            decreases |l| - i
        {
            if l[i] == element
            {
                l := l[..i] + l[i + 1..];
                found := true;
                break;
            }
            i := i + 1;
        }
        assert found;
        assert |l| == |old(l)| - 1;
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
        var actualIndex := index % |l|;
        l := l[..actualIndex] + l[actualIndex + 1..];
        assert |l| == |old(l)| - 1;
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
        requires |l| > 0
        ensures |l| == 1 ==> x == l[0]
        ensures |l| > 1 && index % |l| == (|l| - 1) ==> x == l[0]
        ensures |l| > 1 && 0 <= index && |l| < (|l| - 1) ==> x == l[index % |l| + 1]
    {
        if (|l| == 1)
        {
            x := l[0];
            assert x == l[0];
        }
        else
        {
            var actualIndex := index % |l|;
            if (actualIndex == (|l| - 1))
            {
                x := l[0];
                assert x == l[0];
            } else {
                x := l[actualIndex + 1];
                assert x == l[actualIndex + 1];
            }
        }
        
        return x;
    }

    method isIn(element: T) returns (b: bool)
        ensures |l| == 0 ==> b == false
        ensures |l| > 0 && b == true ==> exists i :: 0 <= i < |l| && l[i] == element
        ensures |l| > 0 && b == false ==> !exist
function abs(a: real) : real {if a>0.0 then a else -a}
