
method {:verify true} FindAllOccurrences(text: string, pattern: string) returns (offsets: set<nat>)
	ensures forall i :: i in offsets ==> i + |pattern| <= |text|
	ensures forall i :: 0 <= i <= |text| - |pattern| ==> (text[i..i+|pattern|] == pattern <==> i in offsets)
{
    offsets := {};
    var i:int := 0;
	// no pattern in text at all.
    if |pattern| > |text|
    {
        return offsets;
    }

	//all offsets are offsets of pattern/ 
    if pattern == ""
    {
        while i < |text|
		invariant 0 <= i <= |text|
		invariant offsets == set j | 0 <= j < i
		{
			offsets := offsets + {i};
            i:=i+1;
		}
        offsets := offsets + {|text|};
		return offsets;
    }

    var pattern_hash: int := RecursiveSumDown(pattern);
    var text_hash: int := RecursiveSumDown(text[..|pattern|]);
    
	if pattern_hash == text_hash{
        if text[..|pattern|] == pattern
        {
            offsets := offsets + {0};
        }
    }
	
    else
	{
        LemmaRabinKarp(text[..|pattern|], pattern, text_hash, pattern_hash);
    }

	while i < |text| - |pattern|
	invariant 0 <= i <= |text| - |pattern|
	invariant offsets == set j | 0 <= j <= i && text[j..j+|pattern|] == pattern
	invariant forall j :: 0 <= j < i ==> (text[j..j+|pattern|] == pattern <==> j in offsets)
	invariant text_hash == RecursiveSumDown(text[i..i+|pattern|])
	{
		//updating text hash
		var old_text_hash := text_hash;
		var left_letter_as_int := text[i] as int;
		var right_new_letter_as_int := text[i+|pattern|] as int;
		text_hash := text_hash - left_letter_as_int + right_new_letter_as_int;
		//updating i
		i := i + 1;
		//checking hash equality
		if pattern_hash == text_hash{
			if text[i..i + |pattern|] == pattern
			{
				offsets := offsets + {i};
			}
			LemmaHashEqualty(text_hash, text, i, old_text_hash, pattern);
		}
		else{
			LemmaHashEqualty(text_hash, text, i, old_text_hash, pattern);
			LemmaRabinKarp(text[i..i+|pattern|], pattern, text_hash, pattern_hash);
		}
		Lemma2Sides(text, pattern, i, offsets);
		//=>
		//=>
	}
	//=>
}

function abs(a: real) : real {if a>0.0 then a else -a}
