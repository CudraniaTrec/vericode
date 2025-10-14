
predicate IsUpperCase(c : char)
{
    65 <= c as int <= 90
}

predicate IsUpperLowerPair(C : char, c : char)
{
    (C as int) == (c as int) - 32
}

function Shift32(c : char) :  char
{
    ((c as int + 32) % 128) as char
}

method ToLowercase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
{
    var s' : string := [];
    var i: int := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |s'| == i
        invariant forall j :: 0 <= j < i ==> if IsUpperCase(s[j]) then IsUpperLowerPair(s[j], s'[j]) else s'[j] == s[j]
    {
        if IsUpperCase(s[i])
        {
            var shifted := Shift32(s[i]);
            assert IsUpperLowerPair(s[i], shifted);
            s' := s' + [shifted];
        }
        else 
        {
            s' := s' + [s[i]];
        }
        i := i + 1;
    }
    v := s';
}

function abs(a: real) : real {if a>0.0 then a else -a}
