method Main() {
	var str1,str2 := "Dafny","fn";
	var found,offset := FindSubstring(str1,str2);
	assert found by
	{
		calc {
			str2 <= str1[2..];
		==>
			IsSubsequenceAtOffset(str1,str2,2);
		==>
			IsSubsequence(str1,str2);
		==
			found;
		}
	}
	assert offset == 2 by
	{
		assert found && str2 <= str1[2..];
		assert offset != 0 by { assert 'D' == str1[0] != str2[0] == 'f'; }
		assert offset != 1 by { assert 'a' == str1[1] != str2[0] == 'f'; }
		assert offset != 3 by { assert 'n' == str1[3] != str2[0] == 'f'; }
		assert !(offset >= 4) by { assert 4 + |str2| > |str1|; }
	}
	print "The sequence ";
	print str2;
	print " is a subsequence of ";
	print str1;
	print " starting at element ";
	print offset;
}


predicate IsSubsequence<T>(q1: seq<T>, q2: seq<T>)
{
	exists offset: nat :: offset + |q2| <= |q1| && IsSubsequenceAtOffset(q1,q2,offset)
}

predicate IsSubsequenceAtOffset<T>(q1: seq<T>, q2: seq<T>, offset: nat)
{ // "<=" on sequences means "is prefix?": "is q2 a prefix of q1[offset..]"
	offset + |q2| <= |q1| && q2 <= q1[offset..]
}


method FindSubstring(str1: string, str2: string) returns (found: bool, offset: nat)
	requires |str2| <= |str1|
	requires |str1| > 0 && |str2| >0
	// a string in Dafny is a sequence of characters: "seq<char>"
	ensures found <== IsSubsequence(str1,str2)
	ensures found ==> IsSubsequence(str1,str2)
	ensures found ==> IsSubsequenceAtOffset(str1,str2,offset)
// TODO: refine this specification into (verified, correct, executable...) code.
{
		offset :=0;
		found := str2 <= str1[0..];
		// checking if str2 is substring of str1 --> loop from 0 to  |str1|-1 
		while(offset <= |str1|-|str2| && !found)
			invariant Inv1(str1,str2,offset,found)
			decreases (|str1|-|str2|) -offset
			{
			  if str2 <= str1[(offset+1)..]
				 { // check if str2 prefix of str1..
					 found:= true;
				}
			offset:=offset+1;
			}
}


method FindSubstring'(str1: string, str2: string) returns (found: bool, offset: nat)
	requires |str2| <= |str1|
	requires |str1| > 0 && |str2| >0
	// a string in Dafny is a sequence of characters: "seq<char>"
	ensures found <== IsSubsequence(str1,str2)
	ensures found ==> IsSubsequence(str1,str2)
	ensures found ==> IsSubsequenceAtOffset(str1,str2,offset)
// TODO: refine this specification into (verified, correct, executable...) code.
{ 
		assert |str2| <= |str1| && |str1| > 0 && |str2| >0 ; // the pre conditions of the method is correct.
		assert Inv1(str1,str2,0,str2 <= str1[0..]);
		offset :=0;
		assert Inv1(str1,str2,offset,str2 <= str1[0..]);
		found := str2 <= str1[0..];
		assert Inv1(str1,str2,offset,found);
		// checking if str2 is substring of str1 --> loop from 0 to  |str1|-1 
		while(offset <= |str1|-|str2| && !found)
			invariant Inv1(str1,str2,offset,found)
			decreases (|str1|-|str2|) -offset
			{
			assert Inv1(str1,str2,offset,found) && (offset <= |str1|-|str2| && !found);	// here the invariant and the loop guard must be correct..
			  if str2 <= str1[(offset+1)..]
				 { // check if str2 prefix of str1..
					 assert Inv1(str1,str2,offset+1,true);
					 found:= true;
					 assert Inv1(str1,str2,offset+1,found);
				 } 

			assert Inv1(str1,str2,offset+1,found);
			offset:=offset+1;
			assert Inv1(str1,str2,offset,found);
			}

			assert Inv1(str1,str2,offset,found);
			assert !(offset <= |str1|-|str2| && !found); // !loop guard
			assert (found <== IsSubsequence(str1,str2)) && (found ==> IsSubsequence(str1,str2)) && (found ==> IsSubsequenceAtOffset(str1,str2,offset));
			// this is the post cond of the method FindSubstring
}


predicate Inv1<T>(str1: seq<T>, str2: seq<T>, offset: nat, found: bool)
{
		 (found <==(exists offset111: nat ::offset111<= offset && offset111 + |str2| <= |str1| && IsSubsequenceAtOffset(str1,str2,offset111)))
	&&	 (found ==>(exists offset: nat :: offset + |str2| <= |str1| && offset + |str2| <= |str1| && str2 <= str1[offset..]))
	&&	  (found ==> IsSubsequenceAtOffset(str1,str2,offset) )
}



	
    

