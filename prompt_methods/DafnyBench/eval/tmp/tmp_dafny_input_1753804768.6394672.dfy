
// Assuming Array is Object Blood
// Blood Array<int>
// index

method Find(blood: array<int>, key: int) returns (index: int)
requires blood != null
ensures 0 <= index ==> index < blood.Length && blood[index] == key
ensures index < 0 ==> forall k :: 0 <= k < blood.Length ==> blood[k] != key
{
   index := 0;
   while index < blood.Length
      invariant 0 <= index <= blood.Length
      invariant forall k :: 0 <= k < index ==> blood[k] != key
   {
      if blood[index] == key { 
         assert 0 <= index < blood.Length;
         assert blood[index] == key;
         return; 
      }
      index := index + 1;
   }
   assert index == blood.Length;
   assert forall k :: 0 <= k < blood.Length ==> blood[k] != key;
   index := -1;
}

function abs(a: real) : real {if a>0.0 then a else -a}
