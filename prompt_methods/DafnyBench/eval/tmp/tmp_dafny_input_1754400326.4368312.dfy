//This method should return true iff pre is a prefix of str. That is, str starts with pre
method isPrefix(pre:string, str:string) returns(res:bool)
    requires 0 < |pre| <= |str|
    ensures res <==> (forall j :: 0 <= j < |pre| ==> pre[j] == str[j])
{
    var i := 0;
    while (i < |pre|)
        invariant 0 <= i <= |pre|
        invariant forall j :: 0 <= j < i ==> pre[j] == str[j]
    {
        if (str[i] != pre[i]) {
            print str[i], " != ", pre[i], "\n";
            return false;
        } else {
            print str[i], " == ", pre[i], "\n";
            i := i + 1;
        }
    }
    return true;
}

// Helper function for isPrefix
function IsPrefixFun(pre: string, str: string): bool
    requires 0 < |pre| <= |str|
{
    forall j :: 0 <= j < |pre| ==> pre[j] == str[j]
}

//This method should return true iff sub is a substring of str. That is, str contains sub
method isSubstring(sub:string, str:string) returns(res:bool)
    requires 0 < |sub| <= |str|
    ensures res <==> (exists j :: 0 <= j <= |str| - |sub| && (forall k :: 0 <= k < |sub| ==> str[j+k] == sub[k]))
{
    var i := 0;
    var n := (|str| - |sub|);
    while(i < n+1)
        invariant 0 <= i <= n+1
        invariant forall j :: 0 <= j < i ==> !IsPrefixFun(sub, str[j..|str|])
    {
        print "\n", sub, ", ", str[i..|str|], "\n";
        var result:= isPrefix(sub, str[i..|str|]);
        if(result == true){
            return true;
        } else{
            i := i+1;
        }
    }
    return false;
}

// Helper function for isSubstring
function IsSubstringFun(sub: string, str: string): bool
    requires 0 < |sub| <= |str|
{
    exists j :: 0 <= j <= |str| - |sub| && (forall k :: 0 <= k < |sub| ==> str[j+k] == sub[k])
}

//This method should return true iff str1 and str1 have a common substring of length k
method haveCommonKSubstring(k:nat, str1:string, str2:string) returns(found:bool)
    requires 0 < k <= |str1| &&  0 < k <= |str2|
    ensures found <==> (exists i, j :: 0 <= i <= |str1|-k && 0 <= j <= |str2|-k && (forall m :: 0 <= m < k ==> str1[i+m] == str2[j+m]))
{
    var i := 0;
    var n := |str1|-k;
    while(i < n)
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < i ==> !IsSubstringFun(str1[j..j+k], str2)
    {
        print "\n", str1[i..i+k], ", ", str2, "\n";
        var result := isSubstring(str1[i..i+k], str2);
        if(result == true){
            return true;
        } else{
            i:=i+1;
        }
    }
    return false;
}

// Helper function for haveCommonKSubstring
function HaveCommonKSubstringFun(k: nat, str1: string, str2: string): bool
    requires 0 < k <= |str1| && 0 < k <= |str2|
{
    exists i, j :: 0 <= i <= |str1|-k && 0 <= j <= |str2|-k && (forall m :: 0 <= m < k ==> str1[i+m] == str2[j+m])
}

//This method should return the natural number len which is equal to the length of the longest common substring of str1 and str2. Note that every two strings have a common substring of length zero.
method maxCommonSubstringLength(str1:string, str2:string) returns(len:nat)
    requires 0 < |str1| && 0 < |str2|
    ensures 0 <= len <= (if |str1| < |str2| then |str1| else |str2|)
    ensures (exists i, j :: 0 <= len && len <= |str1| && len <= |str2| && 0 <= i <= |str1|-len && 0 <= j <= |str2|-len && (forall m :: 0 <= m < len ==> str1[i+m] == str2[j+m]))
    ensures forall l :: len < l <= (if |str1| < |str2| then |str1| else |str2|) ==>
        !(exists i, j :: 0 <= i <= |str1|-l && 0 <= j <= |str2|-l && (forall m :: 0 <= m < l ==> str1[i+m] == str2[j+m]))
{
    var result:bool;
    var i:= |str1|;
    if(|str2| < |str1|){
        i := |str2|;
    }
    while (i > 0)
        invariant 0 <= i <= (if |str1| < |str2| then |str1| else |str2|)
        invariant forall l :: i < l <= (if |str1| < |str2| then |str1| else |str2|) ==>
            !HaveCommonKSubstringFun(l, str1, str2)
    {
        print str1, ", ", str2, " k = ", i, "\n";
        result := haveCommonKSubstring(i, str1, str2);
        if(result == true){
            return i;
        } else{
            i := i - 1;
        }
    }
    return 0;
}

//Main to test each method
method Main(){
    // isPrefix test
    var prefix:string := "pre";
    var str_1:string := "prehistoric";
    var result:bool;
    /*
    result := isPrefix(prefix, str_1);

    if(result == true){
        print "TRUE: ", prefix,  " is a prefix of the string ", str_1, "\n";
    }
    else{
        print "FALSE: ", prefix,  " is not a prefix of the string ", str_1, "\n";
    }
    */
    // isSubstring test
    var substring := "and";
    var str_2 := "operand";
    /*
    result := isSubstring(substring, str_2);

    if(result == true){
        print "TRUE: ", substring,  " is a substring of the string ", str_2, "\n";
    }
    else{
        print "FALSE: ", substring,  " is not a substring of the string ", str_2, "\n";
    }
    */
    // haveCommonKSubstring test
    //these 2 strings share the common substring "ratio" of length 5
    var string1 := "operation";
    var string2 := "irrational";
    var k:nat := 5;
    /*
    result := haveCommonKSubstring(k, string1, string2);

    if(result == true){
        print "TRUE: ", string1, " and ", string2, " have a common substring of length ", k, "\n";
    }
    else{
        print "FALSE: ", string1, " and ", string2, " do not have a common substring of length ", k, "\n";
    }
    */

    var x := maxCommonSubstringLength(string1, string2);
    print "Result: ", x, "\n";
}

function abs(a: real) : real {if a>0.0 then a else -a}
