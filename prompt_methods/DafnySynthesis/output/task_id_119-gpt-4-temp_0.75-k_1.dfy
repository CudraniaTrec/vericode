method FindSingleElement(a: array<int>) returns (single: int)
    requires a != null && a.Length > 0
    requires forall i :: 0 <= i < a.Length - 1 ==> a[i] <= a[i+1]
    requires a.Length % 2 == 1 // Odd length
    ensures exists! i :: 0 <= i < a.Length && a[i] == single
    ensures forall i :: 0 <= i < a.Length ==> 
                (a[i] == single <==> 
                  (forall j :: 0 <= j < a.Length && j != i ==> a[j] != single))
{
    var left := 0;
    var right := a.Length - 1;

    while left < right
        invariant 0 <= left <= right < a.Length
        invariant (right - left) % 2 == 0
    {
        var mid := left + (right - left) / 2;

        if mid % 2 == 1 {
            mid := mid - 1;
        }
        if a[mid] == a[mid + 1] {
            left := mid + 2;
        } else {
            right := mid;
        }
    }
    single := a[left];
}