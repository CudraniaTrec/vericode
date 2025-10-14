
// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type uint32 = i:int | 0 <= i < 0x1_0000_0000

function last<T>(s:seq<T>):T
    requires |s| > 0;
{
    s[|s|-1]
}

function all_but_last<T>(s:seq<T>):seq<T>
    requires |s| > 0;
    ensures  |all_but_last(s)| == |s| - 1;
    ensures  all_but_last(s) + [last(s)] == s;
{
    s[..|s|-1]
}

function ConcatenateSeqs<T>(ss:seq<seq<T>>) : seq<T>
    ensures |ss| == 0 ==> ConcatenateSeqs(ss) == [];
    ensures |ss| > 0 ==> ConcatenateSeqs(ss) == ss[0] + ConcatenateSeqs(ss[1..]);
    ensures |ConcatenateSeqs(ss)| == if |ss| == 0 then 0 else |ss[0]| + |ConcatenateSeqs(ss[1..])|;
{
    if |ss| == 0 then [] else ss[0] + ConcatenateSeqs(ss[1..])
}

lemma {:axiom} lemma_ReverseConcatenateSeqs<T>(ss:seq<seq<T>>)
    requires |ss| > 0;
    ensures  ConcatenateSeqs(ss) == ConcatenateSeqs(all_but_last(ss)) + last(ss);

lemma Test(word_seqs:seq<seq<uint32>>, words:seq<uint32>)
{
    var word_seqs' := word_seqs + [words];

    calc {
        ConcatenateSeqs(word_seqs');
            { lemma_ReverseConcatenateSeqs(word_seqs'); }
        ConcatenateSeqs(all_but_last(word_seqs')) + last(word_seqs');
    }
}

lemma AltTest(word_seqs:seq<seq<uint32>>, words:seq<uint32>)
{
    var word_seqs' := word_seqs + [words];
    assert |word_seqs'| > 0;
    assert all_but_last(word_seqs') + [last(word_seqs')] == word_seqs';
    assert ConcatenateSeqs(word_seqs') == ConcatenateSeqs(all_but_last(word_seqs')) + last(word_seqs');
}

function f<T>(s:seq<T>):seq<T>
    ensures |f(s)| == |s|;
    ensures forall i :: 0 <= i < |s| ==> f(s)[i] == s[i];

function g<T>(ss:seq<seq<T>>) : seq<T>
    ensures |g(ss)| == |ConcatenateSeqs(ss)|;

lemma {:axiom} lemma_fg<T>(s:seq<seq<T>>)
    ensures  g(s) == g(f(s));

lemma Test2(s:seq<seq<uint32>>)
{
    calc {
        g(s);
            { lemma_fg(s); }
        g(f(s));
    }
}

lemma AltTest2(s:seq<seq<uint32>>)
{
    lemma_fg(s);
}

function abs(a: real) : real {if a>0.0 then a else -a}
