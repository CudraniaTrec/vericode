method UniqueProduct (arr: array<int>) returns (product: int)
   ensures product == SetProduct((set i | 0 <= i < arr.Length :: arr[i]))
{
    var p := 1;
    var seen: set<int> := {};
    var i: int := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant seen == (set j | 0 <= j < i :: arr[j])
        invariant p == SetProduct(seen)
    {
        if !(arr[i] in seen) {
            // Before: p == SetProduct(seen)
            // After: seen' == seen + {arr[i]}, p' == p * arr[i]
            SetProductLemma(seen + {arr[i]}, arr[i]);
            p := p * arr[i];
            seen := seen + { arr[i] };
        } else {
            seen := seen;
        }
        i := i + 1;
    }
    assert seen == (set j | 0 <= j < arr.Length :: arr[j]);
    assert p == SetProduct(seen);
    product := p;
}

ghost function SetProduct(s : set<int>) : int
{
    if s == {} then 1
    else var x :| x in s; 
         x * SetProduct(s - {x})
}

/* 
 * This is necessary because, when we add one element, we need to make sure
 * that the product of the new set, as a whole, is the same as the product
 * of the old set times the new element.
 */
lemma SetProductLemma(s: set <int>, x: int) 
 requires x in s
 ensures SetProduct(s) == SetProduct(s - {x}) * x
{
   if s != {}
   {
      var y :| y in s && y * SetProduct(s - {y}) == SetProduct(s);
      if y == x {
         // SetProduct(s) == x * SetProduct(s - {x})
      } else {
         SetProductLemma(s - {y}, x);
         SetProductLemma(s - {x}, y);
      }
   }
}

function abs(a: real) : real {if a>0.0 then a else -a}
