
predicate quickSorted(Seq: seq<int>)
{
  forall idx_1, idx_2 :: 0 <= idx_1 < idx_2 < |Seq| ==> Seq[idx_1] <= Seq[idx_2]
}

method threshold(thres:int,Seq:seq<int>) returns (Seq_1:seq<int>,Seq_2:seq<int>)
  ensures (forall x | x in Seq_1 :: x <= thres) && (forall x | x in Seq_2 :: x >= thres)
  ensures |Seq_1| + |Seq_2| == |Seq| 
  ensures multiset(Seq_1) + multiset(Seq_2) == multiset(Seq)
{
  Seq_1 := [];
  Seq_2 := [];
  var i := 0;
  while (i < |Seq|)
    invariant 0 <= i <= |Seq|
    invariant |Seq_1| + |Seq_2| == i
    invariant multiset(Seq_1) + multiset(Seq_2) == multiset(Seq[..i])
    invariant forall x | x in Seq_1 :: x <= thres
    invariant forall x | x in Seq_2 :: x >= thres
  {
    if (Seq[i] <= thres) {
      Seq_1 := Seq_1 + [Seq[i]];
    } else {
      Seq_2 := Seq_2 + [Seq[i]];
    }
    i := i + 1;
  }
  // At this point, i == |Seq|, so all elements have been partitioned
}

lemma Lemma_1(Seq_1:seq<int>,Seq_2:seq<int>)
  requires multiset(Seq_1) == multiset(Seq_2)
  ensures forall x | x in Seq_1 :: x in Seq_2
{
  // Proof omitted
}

method quickSort(Seq: seq<int>) returns (Seq': seq<int>)
  ensures multiset(Seq) == multiset(Seq')
  decreases |Seq|
{
  if |Seq| == 0 {
    Seq' := [];
    return;
  } else if |Seq| == 1 {
    Seq' := Seq;
    return;
  } else {  
    var Seq_1, Seq_2 := threshold(Seq[0], Seq[1..]);
    var Seq_1' := quickSort(Seq_1);
    Lemma_1(Seq_1', Seq_1);
    var Seq_2' := quickSort(Seq_2);
    Lemma_1(Seq_2', Seq_2);
    Seq' := Seq_1' + [Seq[0]] + Seq_2';
    return;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
