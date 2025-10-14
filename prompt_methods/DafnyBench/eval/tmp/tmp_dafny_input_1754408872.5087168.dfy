
// 2. Given an array of positive and negative integers, it returns an array of the absolute value of all the integers. [-4,1,5,-2,-5]->[4,1,5,2,5]

function abs(a:int):nat
{
    if a < 0 then -a else a
}

method aba(a:array<int>)returns (b:array<int>)
ensures a.Length == b.Length // needed for next line
ensures forall x :: 0<=x<b.Length ==> b[x] == abs(a[x])
{
    
    b := new int[a.Length];
    var i:=0;

    while(i < a.Length)
        invariant 0 <= i <= a.Length
        invariant b != null && b.Length == a.Length
        invariant forall j :: 0 <= j < i ==> b[j] == abs(a[j])
    {
        
        if(a[i] < 0){
            b[i] := -a[i];
            assert b[i] == abs(a[i]);
        } else{
            b[i] := a[i];
            assert b[i] == abs(a[i]);
        }
        i := i + 1;
    }
    

}


method Main()
{
  var a := new int[][1,-2,-2,1];
  var b := aba(a);
  
}

function abs(a: real) : real {if a>0.0 then a else -a}
