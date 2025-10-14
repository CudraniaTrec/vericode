
function SeqRepeat<T>(count:nat, elt:T) : seq<T>
    ensures |SeqRepeat<T>(count, elt)| == count
    ensures forall i :: 0 <= i < count ==> SeqRepeat<T>(count, elt)[i] == elt
{
    if count == 0 then []
    else [elt] + SeqRepeat<T>(count - 1, elt)
}

datatype Maybe<T> = Nothing | Just(v: T)
type Num = x | 0 <= x < 10
datatype D = C(seq<Maybe<Num>>)

lemma test()
{
    ghost var s := SeqRepeat(1, Nothing);
    assert |s| == 1;
    assert forall i :: 0 <= i < 1 ==> s[i] == Nothing;
    ghost var e := C(s);
}

function abs(a: real) : real {if a>0.0 then a else -a}
