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
         return false;                    
      }                                   
      i := i+1;                           
   }                                      
   return true;                           
}     

method TEST()
{
   var a:array<char> := new char[]['r','e','f','e','r'];
   var r:bool := PalVerify(a);
   assert r ==> forall i :: 0 <= i < a.Length/2 ==> a[i] == a[a.Length - i -1];

   var b:array<char> := new char[]['z'];
   r := PalVerify(b);
   assert r ==> forall i :: 0 <= i < b.Length/2 ==> b[i] == b[b.Length - i -1];

   var c:array<char> := new char[][];
   r := PalVerify(c);
   assert r ==> forall i :: 0 <= i < c.Length/2 ==> c[i] == c[c.Length - i -1];

   var d:array<char> := new char[]['x', 'y'];
   r := PalVerify(d);
   assert !r ==> (exists i :: 0 <= i < d.Length/2 && d[i] != d[d.Length - i -1]);

   var e:array<char> := new char[]['1', '2', '3', '4', '2', '1'];
   r := PalVerify(e);
   assert !r ==> (exists i :: 0 <= i < e.Length/2 && e[i] != e[e.Length - i -1]);
}

function abs(a: real) : real {if a>0.0 then a else -a}
