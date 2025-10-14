
method Foo(y: int, x: int) returns (z: int) 
  requires 0 <= y
  ensures z == x*y
{
  var a: int := 0;
  z := 0;
  while a != y 
    invariant 0 <= a <= y
    invariant z == x * a
  {
    z := z + x;
    a := a + 1;
    assert 0 <= a <= y;
    assert z == x * a;
  }
  assert a == y;
  assert z == x * y;
  return z;
}

function stringToSet(s: string): (r: set<char>)
ensures forall x :: 0 <= x < |s| ==> s[x] in r
{
 set x | 0 <= x < |s| :: s[x]
}

//ensures forall a, b :: 0 <= a < b < |s|  ==> forall k, j :: a <=k < j <=b ==> k !=j ==> s[k] != s[j] ==> b-a <= longest
// lemma stringSet(s: string)
//    
//   {
//     if |s| != 0 {


//     }
//   }


method Main() {
	var sample: string := "test";
	var foof := Foo(3,4);
 	var test: set<char> := stringToSet(sample);
 	// var test := set x | 0 <= x < |sample| :: sample[x];
	print foof;
}

function abs(a: real) : real {if a>0.0 then a else -a}
