method AddTupleToList<T1, T2>(lst: seq<(T1, T2)>, tup: (T1, T2)) returns (newLst: seq<(T1, T2)>)
  ensures newLst == lst + [tup]
{
  newLst := lst + [tup];
}