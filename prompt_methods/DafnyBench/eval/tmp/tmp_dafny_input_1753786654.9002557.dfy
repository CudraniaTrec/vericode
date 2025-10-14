function fib(n: nat): nat
{
   if n == 0 then 0 else
   if n == 1 then 1 else
                  fib(n - 1) + fib(n - 2)
}

method fibonacci1(n:nat) returns (f:nat)
ensures f==fib(n)
{
   var i := 0;
   f := 0;
   var fsig := 1;
   while i < n
      invariant 0 <= i <= n
      invariant f == fib(i)
      invariant fsig == fib(i+1)
   {
      f, fsig := fsig, f + fsig;
      i := i + 1;
   }
}

method fibonacci2(n:nat) returns (f:nat)
ensures f==fib(n)
{
if (n==0) {f:=0;}
else{
   var i := 1;
   var fant := 0;
   f := 1;
   while i < n
      invariant 1 <= i <= n
      invariant fant == fib(i-1)
      invariant f == fib(i)
   {
      fant, f := f, fant + f;
      i := i + 1;
   }
}

}

method fibonacci3(n:nat) returns (f:nat)
ensures f==fib(n)
{
   var i: nat := 0;
   var a: nat := 1;
   f := 0; 
   while i < n
      invariant 0 <= i <= n
      invariant f == fib(i)
      invariant (i == 0 ==> a == 1) && (i > 0 ==> a == fib(i-1))
   {
      var tmp := f;
      f := a + f; 
      a := tmp;
      i := i + 1;
   }
}
function abs(a: real) : real {if a>0.0 then a else -a}
