
//This method should return true iff pre is a prefix of str. That is, str starts with pre
method isPrefix(pre:string, str:string) returns(res:bool)
    requires 0 < |pre| <= |str| //This line states that this method requires that pre is less than or equal in length to str. Without this line, an out of bounds error is shown on line 14: "str[i] != pre[i]"
    ensures res <==> (forall j :: 0 <= j < |pre| ==> pre[j] == str[j])
{
    //Initialising the index variable
    var i := 0;

    //Iterating through the first |pre| elements in str
    while (i < |pre|)
        invariant 0 <= i <= |pre|
        invariant forall j :: 0 <= j < i ==> pre[j] == str[j]
    {
        //If an element does not match, return false
        if (str[i] != pre[i]) {
            //Debug print
            print str[i], " != ", pre[i], "\n";

            //Return once mismatch detected, no point in iterating any further
            return false;
        }
        //Else loop until mismatch found or we have reached the end of pre
        else{
            //Debug pront
            print str[i], " == ", pre[i], "\n";

            i := i + 1;
        }
    }
    assert i == |pre|;
    assert forall j :: 0 <= j < |pre| ==> pre[j] == str[j];
    return true;
}

//This method should return true iff sub is a substring of str. That is, str contains sub
method isSubstring(sub:string, str:string) returns(res:bool)
    requires 0 < |sub| <= |str| //This method requires that sub is less than or equal in length to str
    ensures res <==> (exists j :: 0 <= j <= |str| - |sub| && (forall k :: 0 <= k < |sub| ==> str[j+k] == sub[k]))
{
    //Initialising the index variable
    var i := 0;

    //This variable stores the difference in length between the two strings
    var n := (|str| - |sub|);

    while(i < n+1)
        invariant 0 <= i <= n+1
        invariant forall j :: 0 <= j < i ==> !isPrefix(sub, str[j..|str|])
        invariant forall j :: 0 <= j < i ==> (exists k :: 0 <= k < |sub| && str[j+k] != sub[k])
    {
        //Debug print to show what is being passed to isPrefix with each iteration
        print "\n", sub, ", ", str[i..|str|], "\n";

        var result:= isPrefix(sub, str[i..|str|]);

        //Return once the substring is found, no point in iterating any further
        if(result == true){
            return true;
        }
        //Else loop until sub is found, or we have reached the end of str
        else{
            i := i+1;
        }
    }
    assert forall j :: 0 <= j < n+1 ==> !isPrefix(sub, str[j..|str|]);
    return false;
}

//This method should return true iff str1 and str1 have a common substring of length k
method haveCommonKSubstring(k:nat, str1:string, str2:string) returns(found:bool)
    requires 0 < k <= |str1| &&  0 < k <= |str2| //This method requires that k > 0 and k is less than or equal to in length to str1 and str2
    ensures found <==> (exists i, j :: 0 <= i <= |str1|-k && 0 <= j <= |str2|-k && (forall m :: 0 <= m < k ==> str1[i+m] == str2[j+m]))
{
    //Initialising the index variable
    var i := 0;

    //This variable is used to define the end condition of the while loop
    var n := |str1|-k;

    while(i < n)
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < i ==> !isSubstring(str1[j..j+k], str2)
        invariant forall j :: 0 <= j < i ==> (forall l :: 0 <= l <= |str2|-k ==> (exists m :: 0 <= m < k && str1[j+m] != str2[l+m]))
    {
        //Debug print to show what is being passed to isSubstring with each iteration
        print "\n", str1[i..i+k], ", ", str2, "\n";

        var result := isSubstring(str1[i..i+k], str2);

        //Return once the length-k substring is found, no point in iterating any further
        if(result == true){
            return true;
        }
        //Else loop until the length-k substring is found, or we have reached the end condition
        else{
            i:=i+1;
        }
    }
    assert forall j :: 0 <= j < n ==> !isSubstring(str1[j..j+k], str2);
    return false;
}

//This method should return the natural number len which is equal to the length of the longest common substring of str1 and str2. Note that every two strings have a common substring of length zero.
method maxCommonSubstringLength(str1:string, str2:string) returns(len:nat)
    requires 0 < |str1| && 0 < |str1|
    ensures 0 <= len <= if |str1| < |str2| then |str1| else |str2|
    ensures (exists i, j :: 0 <= len && len <= |str1| && len <= |str2| && 0 <= i <= |str1|-len && 0 <= j <= |str2|-len && (forall m :: 0 <= m < len ==> str1[i+m] == str2[j+m]))
    ensures forall l :: len < l <= if |str1| < |str2| then |str1| else |str2| ==>
        !(exists i, j :: 0 <= i <= |str1|-l && 0 <= j <= |str2|-l && (forall m :: 0 <= m < l ==> str1[i+m] == str2[j+m]))
{
    //This variable is used to store the result of calling haveCommonKSubstring
    var result:bool;
    
    //We want the longest common substring between str1 and str2, so the starting point is going to be the shorter of the two strings.
    var i:= |str1|;
    if(|str2| < |str1|){
        i := |str2|;
    }

    //Here, we want to re-use the "haveKCommonSubstring" method above, so with each iteration of the search, we pass a decreasing value of k until a common substring of this length is found. If no common substring is found, we return 0.
    while (i > 0)
        invariant 0 <= i <= if |str1| < |str2| then |str1| else |str2|
        invariant forall l :: i < l <= if |str1| < |str2| then |str1| else |str2| ==>
            !(exists a, b :: 0 <= a <= |str1|-l && 0 <= b <= |str2|-l && (forall m :: 0 <= m < l ==> str1[a+m] == str2[b+m]))
    {
        print str1, ", ", str2, " k = ", i, "\n";
        
        result := haveCommonKSubstring(i, str1, str2);

        if(result == true){
            return i;
        }
        else{
            i := i - 1;
        }
    }
    assert forall l :: 1 <= l <= if |str1| < |str2| then |str1| else |str2| ==>
        !(exists a, b :: 0 <= a <= |str1|-l && 0 <= b <= |str2|-l && (forall m :: 0 <= m < l ==> str1[a+m] == str2[b+m]));
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
