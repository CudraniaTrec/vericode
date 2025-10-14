method ProductOfUnique(arr: array<int>) returns (prod: int)
    requires arr != null
    ensures prod == (
        if |arr| == 0 then 1
        else var uniq := set i | 0 <= i < arr.Length :: arr[i];
            if uniq == {} then 1
            else
                var res := 1;
                forall x :: x in uniq ==> res := res * x;
                res
    )
{
    var uniq := set i | 0 <= i < arr.Length :: arr[i];
    prod := 1;
    // Since Dafny doesn't have a set iterator, we loop over arr and multiply only for the first appearance
    var seen := map<int, bool>{};
    for i := 0 to arr.Length - 1
        invariant 0 <= i <= arr.Length
        invariant forall j :: 0 <= j < i ==> seen[arr[j]] == true
        invariant prod == (if i == 0 then 1 else
            var s := set j | 0 <= j < i :: arr[j];
            if s == {} then 1 else s.Fold(1, (x, y) => x * y)
        )
    {
        if !(arr[i] in seen) {
            prod := prod * arr[i];
            seen := seen[arr[i] := true];
        }
    }
}