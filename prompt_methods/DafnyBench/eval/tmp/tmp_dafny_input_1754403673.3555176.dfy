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
{
    s[..|s|-1]
}

function ConcatenateSeqs<T>(ss:seq<seq<T>>) : seq<T>
{
    if |ss| == 0 then [] else ss[0] + ConcatenateSeqs<T>(ss[1..])
}

lemma {:axiom} lemma_ReverseConcatenateSeqs<T>(ss:seq<seq<T>>)
    requires |ss| > 0;
    ensures  ConcatenateSeqs<T>(ss) == ConcatenateSeqs<T>(all_but_last(ss)) + last(ss);

lemma Test(word_seqs:seq<seq<uint32>>, words:seq<uint32>)
{
    var word_seqs' := word_seqs + [words];

    calc {
        ConcatenateSeqs<uint32>(word_seqs');
            { lemma_ReverseConcatenateSeqs<uint32>(word_seqs'); }
        ConcatenateSeqs<uint32>(all_but_last(word_seqs')) + last(word_seqs');
    }
    assert |word_seqs'| == |word_seqs| + 1;
    assert all_but_last(word_seqs') == word_seqs;
    assert last(word_seqs') == words;
}

lemma AltTest(word_seqs:seq<seq<uint32>>, words:seq<uint32>)
{
    var word_seqs' := word_seqs + [words];
    assert |word_seqs'| == |word_seqs| + 1;
    assert all_but_last(word_seqs') == word_seqs;
    assert last(word_seqs') == words;
}

function f<T>(s:seq<seq<T>>):seq<seq<T>>

function g<T>(ss:seq<seq<T>>) : seq<T>

lemma {:axiom} lemma_fg<T>(s:seq<seq<T>>)
    ensures  g<T>(s) == g<T>(f<T>(s));

lemma Test2(s:seq<seq<uint32>>)
{
    calc {
        g<uint32>(s);
            { lemma_fg<uint32>(s); }
        g<uint32>(f<uint32>(s));
    }
    assert g<uint32>(s) == g<uint32>(f<uint32>(s));
}

lemma AltTest2(s:seq<seq<uint32>>)
{
    lemma_fg<uint32>(s);
    assert g<uint32>(s) == g<uint32>(f<uint32>(s));
}

function abs(a: real) : real {if a>0.0 then a else -a}
