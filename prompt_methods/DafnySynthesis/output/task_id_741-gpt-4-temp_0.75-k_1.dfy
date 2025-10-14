//Dafny Code

method AllCharsSame(s: string) returns (res: bool)
{
    if |s| == 0 {
        // Empty string: conventionally considered "all same"
        res := true;
        return;
    }
    var first := s[0];
    var i := 1;
    while i < |s|
        invariant 1 <= i <= |s|
        invariant forall j :: 0 <= j < i ==> s[j] == first
    {
        if s[i] != first {
            res := false;
            return;
        }
        i := i + 1;
    }
    res := true;
}