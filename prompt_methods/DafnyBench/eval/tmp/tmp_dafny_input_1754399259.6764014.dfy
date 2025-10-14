
method Find(a: array<int>, key: int) returns (index: int)
  ensures -1<=index<a.Length
  ensures index!=-1 ==> a[index]==key && (forall i :: 0 <= i < index ==> a[i] != key)
  ensures index == -1 ==> (forall i::0 <= i < a.Length ==> a[i] != key)
{
  index := 0;
  while index < a.Length
    invariant 0 <= index <= a.Length
    invariant forall i :: 0 <= i < index ==> a[i] != key
  {
    if a[index] == key { 
      assert a[index] == key;
      assert forall i :: 0 <= i < index ==> a[i] != key;
      return; 
    }
    index := index + 1;
  }
  if index >= a.Length  {
    assert index == a.Length;
    assert forall i :: 0 <= i < a.Length ==> a[i] != key;
    index := -1;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
