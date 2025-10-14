
predicate allEqual(s:seq<int>)
{forall i,j::0<=i<|s| && 0<=j<|s| ==> s[i]==s[j] }
//{forall i,j::0<=i<=j<|s| ==> s[i]==s[j] }
//{forall i::0<i<|s| ==> s[i-1]==s[i]} 
//{forall i::0<=i<|s|-1 ==> s[i]==s[i+1]}


//Ordered indexes
lemma equivalenceNoOrder(s:seq<int>)
ensures allEqual(s) <==> forall i,j::0<=i<=j<|s| ==> s[i]==s[j]
{
  // allEqual(s) <==> (forall i,j::0<=i<=j<|s| ==> s[i]==s[j])
  // Forward direction
  assert (allEqual(s)) ==> (forall i,j::0<=i<=j<|s| ==> s[i]==s[j]);
  // Backward direction
  assert (forall i,j::0<=i<=j<|s| ==> s[i]==s[j]) ==> allEqual(s);
}

 
//All equal to first
lemma equivalenceEqualtoFirst(s:seq<int>)
requires s!=[]
ensures allEqual(s) <==> (forall i::0<=i<|s| ==> s[0]==s[i])
{
  // Forward direction
  assert allEqual(s) ==> (forall i::0<=i<|s| ==> s[0]==s[i]);
  // Backward direction
  assert (forall i::0<=i<|s| ==> s[0]==s[i]) ==> allEqual(s);
}



lemma equivalenceContiguous(s:seq<int>)
ensures (allEqual(s) ==> forall i::0<=i<|s|-1 ==> s[i]==s[i+1])
ensures (allEqual(s) <== forall i::0<=i<|s|-1 ==> s[i]==s[i+1])
{
  
  if(|s|==0 || |s|==1){

  }
  else{
    calc {
      forall i::0<=i<|s|-1 ==> s[i]==s[i+1];
      ==>
      {
        equivalenceContiguous(s[..|s|-1]);
      }
      allEqual(s);
    }
  }
  
}



method mallEqual1(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
{
    var i := 0;
    b := true;
    while (i < v.Length && b) 
	  { 
        invariant 0 <= i <= v.Length
        invariant b ==> forall j :: 0 <= j < i ==> v[j] == v[0]
        invariant b ==> i <= v.Length
        invariant b ==> forall j :: 0 <= j < i ==> forall k :: 0 <= k < i ==> v[j] == v[k]
        invariant !b ==> exists j :: 0 <= j < i && v[j] != v[0]
        decreases v.Length - i
        b:=(v[i]==v[0]);
        i := i+1;
    
	  }
    assert b == allEqual(v[0..v.Length]);
}

method mallEqual2(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
{
  var i:int; 
  b:=true;
  
  i:=0;
  while (i < v.Length && v[i] == v[0])
	 {
       invariant 0 <= i <= v.Length
       invariant forall j :: 0 <= j < i ==> v[j] == v[0]
       invariant i <= v.Length
       decreases v.Length - i
       i:=i+1;
	 }
	 b:=(i==v.Length);
     assert b == allEqual(v[0..v.Length]);
}



method mallEqual3(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
{
equivalenceContiguous(v[..]);
 var i:int;
 b:=true;
 if (v.Length >0){
    i:=0;
    while (i<v.Length-1 && v[i]==v[i+1])
    {
      invariant 0 <= i <= v.Length-1
      invariant forall j :: 0 <= j <= i ==> v[j] == v[0]
      invariant forall j :: 0 <= j < i ==> v[j] == v[j+1]
      decreases v.Length-1 - i
      i:=i+1;
    }
    
    b:=(i==v.Length-1);
 }
 assert b == allEqual(v[0..v.Length]);
 }


method mallEqual4(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
{
 var i:int;
 b:=true;
 if (v.Length>0){
    i:=0;
    while (i < v.Length-1 && b)
    {
      invariant 0 <= i <= v.Length-1
      invariant b ==> forall j :: 0 <= j <= i ==> v[j] == v[0]
      invariant b ==> forall j :: 0 <= j < i ==> v[j] == v[j+1]
      invariant !b ==> exists j :: 0 <= j < i && v[j] != v[j+1]
      decreases v.Length-1 - i
	    b:=(v[i]==v[i+1]);
	    i:=i+1;
    }
  }
  assert b == allEqual(v[0..v.Length]);
 }


 method mallEqual5(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
{
    var i := 0;
    b := true;
    while (i < v.Length && b) 
	  { 
        invariant 0 <= i <= v.Length
        invariant b ==> forall j :: 0 <= j < i ==> v[j] == v[0]
        invariant !b ==> exists j :: 0 <= j < i && v[j] != v[0]
        decreases v.Length - i
        if (v[i] != v[0]) { b := false; }
        else { i := i+1;}
  	}
    assert b == allEqual(v[0..v.Length]);
}

function abs(a: real) : real {if a>0.0 then a else -a}
