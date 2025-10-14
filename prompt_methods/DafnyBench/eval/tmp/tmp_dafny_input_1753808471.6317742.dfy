module IntegerSet {

    class Set {

        var elements: seq<int>;

        constructor Set0() 
        ensures this.elements == []
        ensures |this.elements| == 0
        {
            this.elements := [];
        }

        constructor Set(elements: seq<int>)
        requires forall i, j | 0 <= i < |elements| && 0 <= j < |elements| && j != i :: elements[i] != elements[j]
        ensures this.elements == elements
        ensures forall i, j | 0 <= i < |this.elements| && 0 <= j < |this.elements|  && j != i:: this.elements[i] != this.elements[j]
        {
            this.elements := elements;
        }

        method size() returns (size : int)
        ensures size == |elements|
        {
            size := |elements|;
        }

        method addElement(element : int)
        modifies this`elements
        requires forall i, j | 0 <= i < |elements| && 0 <= j < |elements| && j != i :: elements[i] != elements[j]
        ensures element in old(elements) ==> elements == old(elements)
        ensures element !in old(elements) ==> |elements| == |old(elements)| + 1 && element in elements && forall i : int :: i in old(elements) ==> i in elements
        ensures forall i, j | 0 <= i < |elements| && 0 <= j < |elements| && j != i :: elements[i] != elements[j]
        {
            if (element !in elements) {
                elements := elements + [element];
                assert |elements| == |old(elements)| + 1;
                assert element in elements;
                assert forall i : int :: i in old(elements) ==> i in elements;
                assert forall i, j | 0 <= i < |elements| && 0 <= j < |elements| && j != i :: elements[i] != elements[j];
            } else {
                assert elements == old(elements);
            }
        }

        method removeElement(element : int)
        modifies this`elements
        requires forall i, j | 0 <= i < |elements| && 0 <= j < |elements| && j != i :: elements[i] != elements[j]
        ensures element in old(elements) ==> |elements| == |old(elements)| - 1 && (forall i : int :: i in old(elements) && i != element <==> i in elements) && element !in elements
        ensures element !in old(elements) ==> elements == old(elements)
        ensures forall i, j | 0 <= i < |elements| && 0 <= j < |elements| && j != i :: elements[i] != elements[j]
        {
            if (element in elements) {
                var i := 0;
                var n := |elements|;
                while i < n
                    invariant 0 <= i <= n
                    invariant n == |elements|
                    invariant forall k :: 0 <= k < i ==> elements[k] != element
                    decreases n - i
                {
                    if (elements[i] == element) {
                        if (i < n - 1) {
                            elements := elements[..i] + elements[i+1..];
                        } else {
                            elements := elements[..i];
                        }
                        break;
                    }
                    i := i + 1;
                }
                assert element !in elements;
                assert |elements| == |old(elements)| - 1;
                assert forall x : int :: x in old(elements) && x != element <==> x in elements;
                assert forall i, j | 0 <= i < |elements| && 0 <= j < |elements| && j != i :: elements[i] != elements[j];
            } else {
                assert elements == old(elements);
            }
        }

        method contains(element : int) returns (contains : bool)
        ensures contains == (element in elements)
        ensures elements == old(elements)
        {
            contains := false;
            if (element in elements) {
                contains := true;
            }
            assert contains == (element in elements);
            assert elements == old(elements);
        }

        //for computing the length of the intersection of 2 sets
        function intersect_length(s1 : seq<int>, s2 : seq<int>, count : int, start : int, stop : int) : int 
        requires 0 <= start <= stop
        requires stop <= |s1|
        {
            if start == stop then count else (if s1[start] in s2 then intersect_length(s1, s2, count + 1, start + 1, stop) else intersect_length(s1, s2, count, start + 1, stop))
        }

        //for computing the length of the union of 2 sets
        //pass in the length of s2 as the initial count
        function union_length(s1 : seq<int>, s2 : seq<int>, count : int, i : int, stop : int) : int 
        requires 0 <= i <= stop
        requires stop <= |s1|
        {
            if i == stop then count else (if s1[i] !in s2 then union_length(s1, s2, count + 1, i + 1, stop) else union_length(s1, s2, count, i + 1, stop))
        }

        method intersect(s : Set) returns (intersection : Set)
        requires forall i, j | 0 <= i < |s.elements| && 0 <= j < |s.elements| && i != j :: s.elements[i] != s.elements[j]
        requires forall i, j | 0 <= i < |this.elements| && 0 <= j < |this.elements| && i != j :: this.elements[i] != this.elements[j]
        ensures forall i : int :: i in intersection.elements <==> i in s.elements && i in this.elements 
        ensures forall i : int :: i !in intersection.elements  <==> i !in s.elements || i !in this.elements
        ensures forall j, k | 0 <= j < |intersection.elements| && 0 <= k < |intersection.elements| && j != k :: intersection.elements[j] != intersection.elements[k]
        ensures fresh(intersection)
        {
            intersection := new Set.Set0();
            var inter: seq<int> := [];

            var i := 0;
            var n := |this.elements|;
            while i < n
                invariant 0 <= i <= n
                invariant n == |this.elements|
                invariant forall k :: 0 <= k < i ==> (this.elements[k] in s.elements ==> this.elements[k] in inter)
                invariant forall k :: 0 <= k < |inter| ==> inter[k] in this.elements && inter[k] in s.elements
                invariant forall k, l :: 0 <= k < |inter| && 0 <= l < |inter| && k != l ==> inter[k] != inter[l]
                invariant forall x : int :: x in inter <==> (exists k :: 0 <= k < i && this.elements[k] in s.elements && this.elements[k] !in inter[..|inter|] && x == this.elements[k])
                decreases n - i
            {
                if (this.elements[i] in s.elements && this.elements[i] !in inter) {
                    inter := inter + [this.elements[i]];
                }
                i := i + 1;
            }
            intersection.elements := inter;
            assert forall i : int :: i in intersection.elements <==> i in s.elements && i in this.elements;
            assert forall j, k | 0 <= j < |intersection.elements| && 0 <= k < |intersection.elements| && j != k :: intersection.elements[j] != intersection.elements[k];
        }

        method union(s : Set) returns (union : Set)
        requires forall i, j | 0 <= i < |s.elements| && 0 <= j < |s.elements| && i != j :: s.elements[i] != s.elements[j]
        requires forall i, j | 0 <= i < |this.elements| && 0 <= j < |this.elements| && i != j :: this.elements[i] != this.elements[j]
        ensures forall i : int :: i in s.elements || i in this.elements <==> i in union.elements
        ensures forall i : int :: i !in s.elements && i !in this.elements <==> i !in union.elements
        ensures forall j, k | 0 <= j < |union.elements| && 0 <= k < |union.elements| && j != k :: union.elements[j] != union.elements[k]
        ensures fresh(union)
        {
            var elems := s.elements;
            union := new Set.Set0();

            var i := 0;
            var n := |this.elements|;
            while i < n
                invariant 0 <= i <= n
                invariant n == |this.elements|
                invariant forall k :: 0 <= k < i ==> this.elements[k] in elems
                invariant forall x : int :: x in elems <==> x in s.elements || (exists k :: 0 <= k < i && this.elements[k] !in s.elements && x == this.elements[k])
                invariant forall k, l :: 0 <= k < |elems| && 0 <= l < |elems| && k != l ==> elems[k] != elems[l]
                decreases n - i
            {
                if (this.elements[i] !in elems) {
                    elems := elems + [this.elements[i]];
                }
                i := i + 1;
            }

            union.elements := elems;
            assert forall i : int :: i in s.elements || i in this.elements <==> i in union.elements;
            assert forall j, k | 0 <= j < |union.elements| && 0 <= k < |union.elements| && j != k :: union.elements[j] != union.elements[k];
        }
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
