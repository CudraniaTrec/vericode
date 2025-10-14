
method PalVerify(a: array<char>) returns (yn: bool)
ensures yn == true ==> forall i :: 0 <= i < a.Length/2 ==> a[i] == a[a.Length - i -1]
ensures yn == false ==> exists i :: 0 <= i < a.Length/2 && a[i] != a[a.Length - i -1]
ensures forall j :: 0<=j<a.Length ==> a[j] == old(a[j]) 
{
   var i:int := 0;
   while i < a.Length/2
      invariant 0 <= i <= a.Length/2
      invariant forall j :: 0 <= j < i ==> a[j] == a[a.Length - j - 1]
      invariant forall j :: 0<=j<a.Length ==> a[j] == old(a[j])
   {                                      
      if a[i] != a[a.Length-i-1]          
      {                                   
         assert 0 <= i < a.Length/2;
         assert a[i] != a[a.Length-i-1];
         return false;                    
      }                                   
      i := i+1;                           
   }                                      
   assert forall k :: 0 <= k < a.Length/2 ==> a[k] == a[a.Length-k-1];
   return true;                           
}     

method TEST()
{
   var a:array<char> := new char[]['r','e','f','e','r'];
   var r:bool := PalVerify(a);
   assert r;

   var b:array<char> := new char[]['z'];
   r := PalVerify(b);
   assert r;

   var c:array<char> := new char[][];
   r := PalVerify(c);
   assert r;

   var d:array<char> := new char[]['x', 'y'];
   r := PalVerify(d);
   assert !r;

   var e:array<char> := new char[]['1', '2', '3', '4', '2', '1'];
   r := PalVerify(e);
   assert !r;
}

function abs(a: real) : real {if a>0.0 then a else -a}
