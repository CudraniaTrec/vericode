
method Reverse(a: array<int>)
	modifies a;
	ensures forall k :: 0 <= k < a.Length ==> a[k] == old(a[(a.Length-1) - k]);
{
	var l := a.Length - 1;
	var i := 0;
	while (i < l-i)
		invariant 0 <= i <= a.Length
		invariant forall k :: 0 <= k < i ==> a[k] == old(a[l - k])
		invariant forall k :: 0 <= k < i ==> a[l - k] == old(a[k])
		invariant forall k :: i <= k <= l - i ==> a[k] == old(a[k])
		decreases l - 2*i + 1
	{
		a[i], a[l-i] := a[l-i], a[i];
		i := i + 1;
	}
}

method ReverseUptoK(s: array<int>, k: int)
    modifies s
    requires 2 <= k <= s.Length
    ensures forall i :: 0 <= i < k ==> s[i] == old(s[k - 1 - i])
    ensures forall i :: k <= i < s.Length ==> s[i] == old(s[i])
{
	var l := k - 1;
	var i := 0;
	while (i < l-i)
		invariant 0 <= i <= k
		invariant forall j :: 0 <= j < i ==> s[j] == old(s[l - j])
		invariant forall j :: 0 <= j < i ==> s[l - j] == old(s[j])
		invariant forall j :: i <= j <= l - i ==> s[j] == old(s[j])
		invariant forall j :: k <= j < s.Length ==> s[j] == old(s[j])
		decreases l - 2*i + 1
	{
		s[i], s[l-i] := s[l-i], s[i];
		i := i + 1;
	}

}

function abs(a: real) : real {if a>0.0 then a else -a}
