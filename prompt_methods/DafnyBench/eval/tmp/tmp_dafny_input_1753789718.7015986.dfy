
class TwoStacks<T(0)(==)> 
{
    //abstract state
    ghost var s1 :seq<T>
    ghost var s2 :seq<T>
    ghost const N :nat // maximum size of the stacks
    ghost var Repr : set<object>
    //concrete state
    var data: array<T>
    var n1: nat // number of elements in the stack 1
    var n2: nat // number of elements in the stack 2

    ghost predicate Valid()
        reads this,Repr
        ensures Valid() ==> this in Repr &&  |s1| + |s2| <= N && 0 <= |s1| <= N && 0 <=|s2| <= N
    {
        this in Repr && data in Repr && data.Length == N  
         && 0 <= |s1| + |s2| <= N && 0 <=|s1| <= N && 0 <=|s2| <= N
        &&  (|s1| != 0 ==> forall i:: 0<= i < |s1| ==> s1[i] == data[i]) 
        && (|s2| != 0 ==> forall i:: 0<= i < |s2| ==> s2[i] == data[data.Length-1-i])
       && n1 == |s1| && n2 == |s2|
    }

    constructor (N: nat)
        ensures Valid() && fresh(Repr)
        ensures s1 == s2 == [] && this.N == N
    {
        s1,s2,this.N := [],[],N;
        data := new T[N];
        n1, n2 := 0, 0;
        Repr := {this, data};
        assert Valid();
    }
    
    method push1(element:T) returns (FullStatus:bool)
        requires Valid()
        modifies Repr
        ensures old(|s1|) != N && old(|s1|) + old(|s2|) != N ==> s1 ==  old(s1) + [element];
        ensures old(|s1|) == N ==> FullStatus == false
        ensures old(|s1|) != N && old(|s1|) + old(|s2|) == N ==> FullStatus == false
        ensures Valid() && fresh(Repr - old(Repr))
    {   
        if n1  == data.Length
        {   
            FullStatus := false;
        }else {
            if n1 != data.Length && n1 + n2 != data.Length{
                // strongest annotation: n1 < data.Length && n1 + n2 < data.Length
                assert n1 < data.Length;
                assert n1 + n2 < data.Length;
                s1 := old(s1) + [element] ;
                data[n1] := element;
                n1 := n1 +1;
                FullStatus := true;
                assert Valid();
            }else{
                FullStatus := false;
            }
        }
        assert Valid();
    } 

    method push2(element:T) returns (FullStatus:bool)
        requires Valid()
        modifies Repr
        ensures old(|s2|) != N && old(|s1|) + old(|s2|) != N ==> s2 ==  old(s2) + [element];
        ensures old(|s2|) == N ==> FullStatus == false
        ensures old(|s2|) != N && old(|s1|) + old(|s2|) == N ==> FullStatus == false
        ensures Valid() && fresh(Repr - old(Repr))
    {   
        if n2  == data.Length
        {   
            FullStatus := false;
        }else {
            if n2 != data.Length && n1 + n2 != data.Length{
                // strongest annotation: n2 < data.Length && n1 + n2 < data.Length
                assert n2 < data.Length;
                assert n1 + n2 < data.Length;
                s2 := old(s2) + [element] ;
                data[data.Length-1-n2] := element;
                n2 := n2 +1;
                FullStatus := true;
                assert Valid();
            }else{
                FullStatus := false;
            }
        }
        assert Valid();
    } 

    method pop1() returns (EmptyStatus:bool, PopedItem:T)
        requires Valid()
        modifies Repr
        ensures old(|s1|) != 0 ==> s1 == old(s1[0..|s1|-1]) && EmptyStatus == true && PopedItem == old(s1[|s1|-1]) 
        ensures old(|s1|) == 0 ==> EmptyStatus == false 
        ensures Valid() && fresh(Repr - old(Repr))
    {
        if n1 == 0 { 
            EmptyStatus := false;
            PopedItem := *;
        } else{
            // strongest annotation: n1 > 0
            assert n1 > 0;
            assert |s1| > 0;
            s1 := old(s1[0..|s1|-1]);
            PopedItem := data[n1-1];
            n1 := n1 -1;
            EmptyStatus := true;
            assert Valid();
        }
        assert Valid();
    }

    method pop2() returns (EmptyStatus:bool, PopedItem:T)
        requires Valid()
        modifies Repr
        ensures old(|s2|) != 0 ==> s2 == old(s2[0..|s2|-1]) && EmptyStatus == true && PopedItem == old(s2[|s2|-1]) 
        ensures old(|s2|) == 0 ==> EmptyStatus == false 
        ensures Valid() && fresh(Repr - old(Repr))
    {
        if n2 == 0 { 
            EmptyStatus := false;
            PopedItem := *;
        } else{
            // strongest annotation: n2 > 0
            assert n2 > 0;
            assert |s2| > 0;
            s2 := old(s2[0..|s2|-1]);
            PopedItem := data[data.Length-n2];
            n2 := n2 -1;
            EmptyStatus := true;
            assert Valid();
        }
        assert Valid();
    }

    method peek1() returns (EmptyStatus:bool, TopItem:T)
        requires Valid()
        ensures Empty1() ==> EmptyStatus == false
        ensures !Empty1() ==> EmptyStatus == true && TopItem == s1[|s1|-1] 
        ensures Valid()
    {
        if n1 == 0 {
            EmptyStatus := false;
            TopItem := *;
        } else {
            // strongest annotation: n1 > 0
            assert n1 > 0;
            assert |s1| > 0;
            TopItem := data[n1-1];
            EmptyStatus := true;
        }
        assert Valid();
    }

    method peek2() returns (EmptyStatus:bool, TopItem:T)
        requires Valid()
        ensures Empty2() ==> EmptyStatus == false
        ensures !Empty2() ==> EmptyStatus == true && TopItem == s2[|s2|-1] 
        ensures Valid()
    {
        if n2 == 0 {
            EmptyStatus := false;
            TopItem := *;
        } else {
            // strongest annotation: n2 > 0
            assert n2 > 0;
            assert |s2| > 0;
            TopItem := data[data.Length-n2];
            EmptyStatus := true;
        }
        assert Valid();
    }
    
    ghost predicate Empty1() 
        requires Valid()
        reads this,Repr
        ensures Empty1() ==> |s1| == 0
        ensures Valid()
    {
        |s1| == 0 && n1 == 0
    }

    ghost predicate Empty2() 
        reads this
        ensures Empty2() ==> |s2| == 0
    {
        |s2| == 0 && n2 == 0
    }
    
    method search1(Element:T) returns (position:int)
        requires Valid()
        ensures position == -1 || position >= 1
        ensures position >= 1 ==> exists i::0 <=i < |s1| && s1[i] == Element && !Empty1()
        ensures position == -1 ==> forall i :: 0 <= i < |s1| ==> s1[i] != Element || Empty1()
        ensures Valid()
    {
        var n := 0;
        position := 0;

        while n != n1
            invariant 0 <= n <= n1
            invariant n1 == |s1|
            invariant Valid()
            invariant forall k :: 0 <= k < n ==> data[n1-1-k] != Element
            invariant position == 0
        {
            if data[n1-1-n] == Element 
            {
                position := n + 1;
                assert 1 <= position <= n1;
                assert s1[n1-position] == Element;
                assert !Empty1();
                return position; 
            }
            n := n + 1;
        }
        position := -1;
        assert forall i :: 0 <= i < n1 ==> data[n1-1-i] != Element;
        assert forall i :: 0 <= i < |s1| ==> s1[i] != Element || Empty1();
        assert Valid();
    }

    method search3(Element:T) returns (position:int)
        requires Valid()
        ensures position == -1 || position >= 1
        ensures position >= 1 ==> exists i::0 <=i < |s2| && s2[i] == Element && !Empty2()
      //  ensures position == -1 ==> forall i :: 0 <= i < |s2| ==> s2[i] != Element || Empty2()
        ensures Valid()
    {
        position := 0;
        var n := 0;

        while n != n2
            invariant 0 <= n <= n2
            invariant n2 == |s2|
            invariant Valid()
            invariant forall k :: 0 <= k < n ==> data[data.Length - n2 + k] != Element
            invariant position == 0
        {
            if data[data.Length - n2 + n] == Element 
            {
                position :=  n + 1;
                assert 1 <= position <= n2;
                assert s2[n2-position] == Element;
                assert !Empty2();
                return position; 
            }
            n := n + 1;
        }
        
        position := -1;
        assert forall i :: 0 <= i < n2 ==> data[data.Length - n2 + i] != Element;
        assert Valid();
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
