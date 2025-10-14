// RUN: %dafny /compile:4 /compileTarget:cs "%s" > "%t"
// RUN: %dafny /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var a := new int[10];
  var index := 6;
  a[8] := 1;
  a[index], index := 3, index+1;
  // index == 7, a[6] == 3, a[7] == 0, a[8] == 1
  print index, " ", a[6], a[7], a[8], "\n";  // Should be: "7 301"
  index, a[index] := index+1, 9;
  // index == 8, a[7] == 9, a[8] == 1
  expect a[8] == 1; // This failed before the bug fix
  print index, " ", a[6], a[7], a[8], "\n";  // Should be "8 391" not "8 309"

  a[index+1], index := 7, 6;
  // a[9] == 7, index == 6
  expect a[9] == 7 && index == 6;

  var o := new F(2);
  var oo := o;
  print o.f, " ", oo.f, "\n";
  var ooo := new F(4);
  o.f, o := 5, ooo;
  // oo.f == 5, o.f == 4
  print o.f, " ", oo.f, "\n";
  var oooo := new F(6);
  o, o.f := oooo, 7;
  // ooo.f == 7, o.f == 6
  expect ooo.f == 7;  // This failed before the bug fix
  print o.f, " ", ooo.f, "\n";

  var aa := new int[9,9];
  var j := 4;
  var k := 5;
  aa[j,k] := 8;
  j, k, aa[j,k] := 2, 3, 7;
  // j == 2, k == 3, aa[4,5] == 7, aa[2,3] == 0
  print j, " ", k, " ", aa[4,5], " ", aa[2,3], "\n"; // Should be 2 3 7 0
  expect aa[4,5] == 7; // This failed before the bug fix
  j, aa[j,k], k := 5, 6, 1;
  // j == 5, aa[2,3] == 6, k == 1
  expect j == 5 && aa[2,3] == 6 && k == 1; // This failed before the bug fix
  aa[j,k], k, j := 5, 6, 1;
  // j == 1, aa[5,1] == 5, k == 6
  expect j == 1 && aa[5,1] == 5 && k == 6;
}

class F {
  var f: int;
  constructor (f: int) ensures this.f == f { this.f := f; }
}

function abs(a: real) : real {if a>0.0 then a else -a}
