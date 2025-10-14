
method Main() {
   var i := 2;
   var s := [1, i, 3, 4, 5];
   assert |s| == 5;
   assert i == 2;
   assert s[1] == 2;
   print |s|; //size

}

method foo (s: seq<int>)
requires |s| > 1
{
    assert 1 < |s|;
    print s[1];
}

function abs(a: real) : real {if a>0.0 then a else -a}
