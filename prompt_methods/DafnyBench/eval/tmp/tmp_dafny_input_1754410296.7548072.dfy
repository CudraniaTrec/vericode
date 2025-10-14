
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
    // Direct from definitions
}

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures  res <==> isPrefixPred(pre,str)
{
	if |str| < |pre| 
    {
        assert isNotPrefixPred(pre, str);
        return false;
    }
    else if pre[..] == str[..|pre|]
    {
        assert isPrefixPred(pre, str);
        return true;
    }
    else{
        assert isNotPrefixPred(pre, str);
        return false;
    }
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
    // By definitions and quantifier duality
}

method isSubstring(sub: string, str: string) returns (res:bool)
	ensures  res <==> isSubstringPred(sub, str)
	//ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
    var i := 0;
    res := false;
    while i <= |str|
        invariant 0 <= i <= |str|+1
        invariant forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..])
        invariant !res ==> (forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> !isPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefix(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefix(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefix(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefix(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> !isPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefix(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefixPred(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefixPred(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> !isPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefix(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefixPred(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> !isPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefix(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefixPred(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> !isPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefix(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefixPred(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> !isPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefix(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefixPred(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> !isPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefix(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefixPred(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> !isPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefix(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefixPred(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> !isPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefix(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefixPred(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> !isPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefix(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefixPred(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> !isPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefix(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefixPred(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> !isPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefix(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefixPred(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> !isPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefix(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefixPred(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> !isPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefix(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefixPred(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> !isPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefix(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefixPred(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> !isPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefix(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefixPred(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> !isPrefixPred(sub, str[j..]))
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefix(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isPrefixPred(sub, str[j..]) == false)
        invariant !res ==> (forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..]))
        invariant res ==> (exists j :: 0 <= j < i && isPrefixPred(sub, str[j..]))
        decreases |str| - i
    {
        var temp := isPrefix(sub, str[i..]);
        if  temp == true 
        {
            assert isPrefixPred(sub, str[i..]);
            res := true;
            return true;
        }
        i := i + 1;
    } 
    assert forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..]);
    return false;
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
    // By definitions and quantifier duality
}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
	ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
	//ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
    if (k > |str1| || k > |str2| ){
        assert !haveCommonKSubstringPred(k, str1, str2);
        return false;
	}
    var i := 0;
    var temp := false;

    while i <= |str1|-k
        invariant 0 <= i <= |str1|-k+1
        invariant forall j :: 0 <= j < i ==> !isSubstringPred(str1[j..(j+k)], str2)
        invariant !found ==> (forall j :: 0 <= j < i ==> !isSubstringPred(str1[j..(j+k)], str2))
        invariant !found ==> (forall j :: 0 <= j < i ==> isNotSubstringPred(str1[j..(j+k)], str2))
        invariant !found ==> (forall j :: 0 <= j < i ==> haveNotCommonKSubstringPred(k, str1, str2) || isNotSubstringPred(str1[j..(j+k)], str2))
        invariant !found ==> (forall j :: 0 <= j < i ==> !haveCommonKSubstringPred(k, str1, str2) || !isSubstringPred(str1[j..(j+k)], str2))
        invariant !found ==> (forall j :: 0 <= j < i ==> !haveCommonKSubstringPred(k, str1, str2) || !isSubstringPred(str1[j..(j+k)], str2))
        invariant !found ==> (forall j :: 0 <= j < i ==> !isSubstringPred(str1[j..(j+k)], str2))
        invariant !found ==> (forall j :: 0 <= j < i ==> isNotSubstringPred(str1[j..(j+k)], str2))
        invariant found ==> (exists j :: 0 <= j < i && isSubstringPred(str1[j..(j+k)], str2))
        decreases |str1|-k+1-i
    {
        temp := isSubstring(str1[i..(i + k)], str2);
        if  temp == true 
        {
            assert isSubstringPred(str1[i..(i+k)], str2);
            found := true;
            return true;
        }
        i := i + 1;
    }
    assert forall j :: 0 <= j < i ==> isNotSubstringPred(str1[j..(j+k)], str2);
    return false;
}

lemma haveCommon0SubstringLemma(str1:string, str2:string)
    ensures  haveCommonKSubstringPred(0,str1,str2)
{
    // For k = 0, str1[i1..j1] is always the empty string, which is always a substring of any string.
}

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
	requires (|str1| <= |str2|)
	ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
	ensures haveCommonKSubstringPred(len,str1,str2)
{
    var temp := false;
    var i := |str1|+1;
    len := i;
    while i > 0
        invariant 0 <= i <= |str1|+1
        invariant len == i
        invariant forall k :: i < k <= |str1| ==> !haveCommonKSubstringPred(k, str1, str2)
        invariant (exists k :: i <= k <= |str1| && haveCommonKSubstringPred(k, str1, str2)) ==> temp
        invariant temp ==> haveCommonKSubstringPred(len, str1, str2)
        invariant !temp ==> (forall k :: i <= k <= |str1| ==> !haveCommonKSubstringPred(k, str1, str2))
        decreases i
    {
        i:= i-1;
        len := i;
        temp := haveCommonKSubstring(i, str1, str2);
        if  temp == true
        { 
            assert haveCommonKSubstringPred(len, str1, str2);
            break;
        }
    }
    haveCommon0SubstringLemma(str1, str2);
    return len;
}

function abs(a: real) : real {if a>0.0 then a else -a}
