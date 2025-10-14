method Filter(a:seq<char>, b:set<char>) returns(c:set<char>) 
ensures forall x :: x in a && x in b <==> x in c
{
    // Collect all characters from a that are also in b
    c := {};
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant c == { x | 0 <= j < i && x == a[j] && x in b }
    {
        if a[i] in b {
            c := c + {a[i]};
        }
        i := i + 1;
    }
    assert forall x :: x in a && x in b <==> x in c;
}

method TesterFilter()
{
   var v:set<char> := {'a','e','i','o','u'}; // vowels to be used as a filter

   var s:seq<char> := "ant-egg-ink-owl-urn";
   var w:set<char> := Filter(s, v);
   assert forall x :: x in s && x in v <==> x in w;

   s := "nice-and-easy";
   w := Filter(s, v);
   assert forall x :: x in s && x in v <==> x in w;

   s := "mssyysywbrpqsxmnlsghrytx"; // no vowels
   w := Filter(s, v);
   assert forall x :: x in s && x in v <==> x in w;

   s := "iiiiiiiiiiiii";       // 1 vowel
   w := Filter(s, v);
   assert forall x :: x in s && x in v <==> x in w;

   s := "aeiou";          // s == v
   w := Filter(s, v);
   assert forall x :: x in s && x in v <==> x in w;

   s := "u";              // edge singleton
   w := Filter(s, v);
   assert forall x :: x in s && x in v <==> x in w;

   s := "f";              // edge singleton
   w := Filter(s, v);
   assert forall x :: x in s && x in v <==> x in w;

   s := "";               // edge empty seq
   w := Filter(s, v);
   assert forall x :: x in s && x in v <==> x in w;

   v := {};               // edge empty filter
   s := "Any sequence that I like!!!";
   w := Filter(s, v);
   assert forall x :: x in s && x in v <==> x in w;
}
function abs(a: real) : real {if a>0.0 then a else -a}
