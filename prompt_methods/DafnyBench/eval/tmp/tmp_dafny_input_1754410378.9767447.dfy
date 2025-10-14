
predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && 
	pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string)
{
	(|pre| > |str|) || 
	pre != str[..|pre|]
}

lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{
	assert isPrefixPred(pre,str) ==> !isNotPrefixPred(pre,str);
	assert !isNotPrefixPred(pre,str) ==> isPrefixPred(pre,str);
	assert !isPrefixPred(pre,str) ==> isNotPrefixPred(pre,str);
	assert isNotPrefixPred(pre,str) ==> !isPrefixPred(pre,str);
}

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures  res <==> isPrefixPred(pre,str)
{
	return |pre| <= |str| && forall i :: 0 <= i < |pre| ==> pre[i] == str[i];
}

predicate isSubstringPred(sub:string, str:string)
{
	(exists i :: 0 <= i <= |str| &&  isPrefixPred(sub, str[i..]))
}

predicate isNotSubstringPred(sub:string, str:string)
{
	(forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub,str[i..]))
}

lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{
	assert isSubstringPred(sub,str) ==> !isNotSubstringPred(sub,str);
	assert !isNotSubstringPred(sub,str) ==> isSubstringPred(sub,str);
	assert !isSubstringPred(sub,str) ==> isNotSubstringPred(sub,str);
	assert isNotSubstringPred(sub,str) ==> !isSubstringPred(sub,str);
}

method isSubstring(sub: string, str: string) returns (res:bool)
	ensures  res <==> isSubstringPred(sub, str)
	ensures  res ==> isSubstringPred(sub, str)
	// ensures  !res ==> !isSubstringPred(sub, str)
	ensures  isSubstringPred(sub, str) ==> res
	ensures  isSubstringPred(sub, str) ==> res
	ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
	if(|str| < |sub|)
	{
		return false;
	}
	else
	{
		var i: nat := 0;
	 	res := false;
		while (i <= |str|-|sub| && res == false)
			invariant 0 <= i <= |str| - |sub| + 1
			invariant forall j :: 0 <= j < i ==> !isPrefixPred(sub, str[j..])
			invariant res ==> (exists j :: 0 <= j < i && isPrefixPred(sub, str[j..]))
			invariant !res ==> (forall j :: 0 <= j < i ==> !isPrefixPred(sub, str[j..]))
			invariant res ==> isSubstringPred(sub, str)
			invariant !res ==> (forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..]))
		{
			res := isPrefix(sub,str[i..]);
			if(!res)
			{
				i := i + 1;
			}
		}
		// After the loop: either res==true (found), or i > |str|-|sub| and all prefixes failed
		assert res ==> isSubstringPred(sub, str);
		assert !res ==> (forall j :: 0 <= j <= |str| - |sub| ==> !isPrefixPred(sub, str[j..]));
	}
}

predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	exists i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2)
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	forall i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k ==>  isNotSubstringPred(str1[i1..j1],str2)
}

lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==>  haveNotCommonKSubstringPred(k,str1,str2)
{
	assert haveCommonKSubstringPred(k,str1,str2) ==> !haveNotCommonKSubstringPred(k,str1,str2);
	assert !haveNotCommonKSubstringPred(k,str1,str2) ==> haveCommonKSubstringPred(k,str1,str2);
	assert !haveCommonKSubstringPred(k,str1,str2) ==> haveNotCommonKSubstringPred(k,str1,str2);
	assert haveNotCommonKSubstringPred(k,str1,str2) ==> !haveCommonKSubstringPred(k,str1,str2);
}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
	ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
	ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
	if (k <= |str1| && k <= |str2|)
	{
		var slice : string;
		found := false;
		var i: nat := 0;

		while (i <= |str1| - k && found == false)
			invariant 0 <= i <= |str1| - k + 1
			invariant forall j :: 0 <= j < i ==> !isSubstringPred(str1[j..j+k], str2)
			invariant found ==> (exists j :: 0 <= j < i && isSubstringPred(str1[j..j+k], str2))
			invariant !found ==> (forall j :: 0 <= j < i ==> !isSubstringPred(str1[j..j+k], str2))
			invariant found ==> haveCommonKSubstringPred(k, str1, str2)
			invariant !found ==> (forall j :: 0 <= j < i ==> isNotSubstringPred(str1[j..j+k], str2))
		{
			slice := str1[i..i+k];
			found := isSubstring(slice, str2);
			i := i + 1;
		}
		// After the loop: either found==true (found), or i > |str1|-k and all substrings failed
		assert found ==> haveCommonKSubstringPred(k, str1, str2);
		assert !found ==> (forall j :: 0 <= j <= |str1| - k ==> !isSubstringPred(str1[j..j+k], str2));
	} else {
		return false;
	}
}

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
	requires (|str1| <= |str2|)
	ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
	ensures haveCommonKSubstringPred(len,str1,str2)
{
	len := |str1|;
	var hasCommon : bool := true;
	while(len > 0)
		invariant 0 <= len <= |str1|
		invariant (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k, str1, str2))
		invariant hasCommon ==> haveCommonKSubstringPred(len, str1, str2)
	{
		hasCommon := haveCommonKSubstring(len, str1, str2);
		if(hasCommon){
			assert haveCommonKSubstringPred(len, str1, str2);
			return len;
		}
		len := len - 1;
	}
	assert len == 0;
	assert (forall k :: 0 < k <= |str1| ==> !haveCommonKSubstringPred(k, str1, str2));
	assert haveCommonKSubstringPred(len, str1, str2); // len==0
	return len;
}

function abs(a: real) : real {if a>0.0 then a else -a}
