
static lemma lemma_vacuous_statement_about_a_sequence(intseq:seq<int>, j:int)
    requires 0<=j<|intseq|;
    ensures intseq[0..j]==intseq[..j];
{
    // By definition, s[..j] == s[0..j]
    assert intseq[0..j] == intseq[..j];
}

static lemma lemma_painful_statement_about_a_sequence(intseq:seq<int>)
    ensures intseq==intseq[..|intseq|];
{
    // By definition, s[..|s|] == s
    assert intseq == intseq[..|intseq|];
}

static lemma lemma_obvious_statement_about_a_sequence(boolseq:seq<bool>, j:int)
    requires 0<=j<|boolseq|-1;
    ensures boolseq[1..][j] == boolseq[j+1];
{
    // boolseq[1..][j] == boolseq[1 + j] == boolseq[j+1]
    assert boolseq[1..][j] == boolseq[j+1];
}

static lemma lemma_obvious_statement_about_a_sequence_int(intseq:seq<int>, j:int)
    requires 0<=j<|intseq|-1;
    ensures intseq[1..][j] == intseq[j+1];
{
    // intseq[1..][j] == intseq[1 + j] == intseq[j+1]
    assert intseq[1..][j] == intseq[j+1];
}

static lemma lemma_straightforward_statement_about_a_sequence(intseq:seq<int>, j:int)
    requires 0<=j<|intseq|;
    ensures intseq[..j] + intseq[j..] == intseq;
{
    // By definition of sequence concatenation and slicing
    assert intseq[..j] + intseq[j..] == intseq;
}

static lemma lemma_sequence_reduction(s:seq<int>, b:nat)
    requires 0<b<|s|;
    ensures s[0..b][0..b-1] == s[0..b-1];
{
    var t := s[0..b];
    // s[0..b][0..b-1] == s[0..b-1]
    // Prove elementwise
    forall (i | 0<=i<b-1)
        ensures s[0..b][0..b-1][i] == s[0..b-1][i];
    {
        // s[0..b][0..b-1][i] == s[0..b][i] == s[i] == s[0..b-1][i]
        assert s[0..b][0..b-1][i] == s[0..b][i];
        assert s[0..b][i] == s[i];
        assert s[0..b-1][i] == s[i];
    }
    assert s[0..b][0..b-1] == s[0..b-1];
}

static lemma lemma_seq_concatenation_associative(a:seq<int>, b:seq<int>, c:seq<int>)
    ensures (a+b)+c == a+(b+c);
{
    // By associativity of sequence concatenation
    assert (a+b)+c == a+(b+c);
}

static lemma lemma_subseq_concatenation(s: seq<int>, left: int, middle: int, right: int)
    requires 0 <= left <= middle <= right <= |s|;
    ensures s[left..right] == s[left..middle] + s[middle..right];
{
    // By definition of slicing and concatenation
    assert s[left..right] == s[left..middle] + s[middle..right];
}

static lemma lemma_seq_equality(a:seq<int>, b:seq<int>, len:int)
    requires |a| == |b| == len;
    requires forall i {:trigger a[i]}{:trigger b[i]} :: 0 <= i < len ==> a[i] == b[i];
    ensures a == b;
{
    // By extensionality of sequences
    assert |a| == |b|;
    assert forall i :: 0 <= i < len ==> a[i] == b[i];
    assert a == b;
}

static lemma lemma_seq_suffix(s: seq<int>, prefix_length: int, index: int)
    requires 0 <= prefix_length <= index < |s|;
    ensures s[index] == s[prefix_length..][index - prefix_length];
{
    // s[prefix_length..][index - prefix_length] == s[prefix_length + (index - prefix_length)] == s[index]
    assert s[prefix_length..][index - prefix_length] == s[index];
}

function abs(a: real) : real {if a>0.0 then a else -a}
