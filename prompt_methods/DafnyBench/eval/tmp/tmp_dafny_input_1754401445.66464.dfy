//Given an array of characters, it filters all the vowels. [‘d’,’e’,’l’,’i’,’g’,’h’,’t’]-> [’e’,’i’]
const vowels: set<char> := {'a', 'e', 'i', 'o', 'u'}

function FilterVowels(xs: seq<char>): seq<char>
{
    if |xs| == 0 then []
    else if xs[|xs|-1] in vowels then FilterVowels(xs[..|xs|-1]) + [xs[|xs|-1]]
    else FilterVowels(xs[..|xs|-1])
}

method FilterVowelsArray(xs: array<char>) returns (ys: array<char>)
    ensures fresh(ys)
    ensures FilterVowels(xs[..]) == ys[..]
{
    var n := 0;
    var i := 0;
    while i < xs.Length
        invariant 0 <= i <= xs.Length
        invariant 0 <= n <= i
        invariant n == |FilterVowels(xs[..i])|
    {
        if xs[i] in vowels {
            n := n + 1;
        }
        i := i + 1;
    }

    ys := new char[n];
    i := 0;
    var j := 0;
    while i < xs.Length
        invariant 0 <= i <= xs.Length
        invariant 0 <= j <= n
        invariant j == |FilterVowels(xs[..i])|
        invariant ys[..j] == FilterVowels(xs[..i])
    {
        if xs[i] in vowels {
            ys[j] := xs[i];
            j := j + 1;
        }
        i := i + 1;
    }
    assert j == n;
    assert ys[..] == FilterVowels(xs[..]);
}

function abs(a: real) : real {if a>0.0 then a else -a}
