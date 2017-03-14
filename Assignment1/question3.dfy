method Main() {
	var qs: seq<seq<int>> :=
		[[ 1, 3,-2, 7, 0],
		 [-1,-2, 2,17,-5],
		 [ 2, 2, 1,-4,-3],
		 [ 0, 0, 1, 7,17],
		 [-2, 8,-2, 2, 8]];

	var min,max := ExtremeElements(qs);

	assert min == -5 && max == 17 by
	{
		assert qs[1][4] == -5;
		assert qs[3][4] == 17;
		assert forall i,j :: 0 <= i < 5 && 0 <= j < 5 ==> -5 <= qs[i][j] <= 17;
	}

	print "The smallest element in ";
	print qs;
	print " is ";
	print min;
	print " and the largest element is ";
	print max;
}


method ExtremeElements(qs: seq<seq<int>>) returns (min: int, max: int)
	requires qs != [] && qs[0] != []
	ensures exists row: nat :: row < |qs| && min in qs[row]
	ensures exists row: nat :: row < |qs| && max in qs[row]
	ensures forall row: nat, column: nat :: row < |qs| && column < |qs[row]| ==> min <= qs[row][column] <= max
{
	min, max := qs[0][0], qs[0][0];
	var i: nat,j: nat := 0,1;
	while i != |qs|
		invariant Inv1(qs,i,j,min,max)
		decreases |qs|-i
	{
		i,j,min,max := EE1(qs,i,j,min,max);
	}
}

method EE1(qs: seq<seq<int>>, i0: nat, j0: nat, min0: int, max0: int) returns (i: nat, j: nat, min: int, max: int)
	requires Inv1(qs,i0,j0,min0,max0)
	requires i0 != |qs|
	ensures Inv1(qs,i,j,min,max)
	ensures 0 <= |qs|-i < |qs|-i0
// TODO: refine the specification of this method into (verified, correct, executable...) code.
	{
	min:=min0;
	max:=max0;
	i:=i0;
	j:=j0;
	while j != |qs[i]|
		invariant Inv1(qs,i,j,min,max)
		decreases |qs[i]|-j
	{		
			if(qs[i][j]>max) {
				max:=qs[i][j];
				}

			if(qs[i][j]<min) {
				min:=qs[i][j];
				}
			j:=j+1;
	}
	i:=i+1;
	j:=0;
}



//This version have a proof with asserts to give correctnes of the program..
method EE1'(qs: seq<seq<int>>, i0: nat, j0: nat, min0: int, max0: int) returns (i: nat, j: nat, min: int, max: int)
	requires Inv1(qs,i0,j0,min0,max0)
	requires i0 != |qs|
	ensures Inv1(qs,i,j,min,max)
	ensures 0 <= |qs|-i < |qs|-i0
// TODO: refine the specification of this method into (verified, correct, executable...) code.
	{
	// at the first of the EE1 method we must to check the pre conditions so-->
	assert  Inv1(qs,i0,j0,min0,max0) && i0 != |qs|; // pre-conditions of the EE1 methods (the requeries)

	assert Inv1(qs,i0,j0,min0,max0) ;// pre-cond of down subsition
	min:=min0;
	assert Inv1(qs,i0,j0,min,max0) ;// post-cond of up substitution
	assert Inv1(qs,i0,j0,min,max0) ;// pre-cond of down subsition
	max:=max0;
	assert Inv1(qs,i0,j0,min,max) ;// post-cond of up subsition
	assert Inv1(qs,i0,j0,min,max) ;// pre-cond of down subsition
	i:=i0;
	assert Inv1(qs,i,j0,min,max) ;// post-cond of up subsition
	assert Inv1(qs,i,j0,min,max) ;// pre-cond of down subsition
	j:=j0;
	assert Inv1(qs,i,j,min,max) ;//// post-cond of up subsition

	assert Inv1(qs,i,j,min,max)  ;//now we want to assert that the invariant of the while is correct before we insert to the while loop.

	while j != |qs[i]|
		invariant Inv1(qs,i,j,min,max)
		decreases |qs[i]|-j
	{		
		assert Inv1(qs,i,j,min,max) && j != |qs[i]|; //(INV&& GUARD) here we must check correctnes of Inv && guard because we know from the class lectures that
		// at the begining of the while body the invariant and the guard must be correct.

		assert j != |qs[i]| && j <= |qs[i]| ==> j != |qs[i]|;
		assert  j != |qs[i]| ==> j+1 <=|qs[i]|;
		assert 0<=j<|qs[i]|;

			if(qs[i][j]>max) {
				assert Inv1(qs,i,j+1,min,qs[i][j]);// pre cond of the subsituition
				max:=qs[i][j];
				assert Inv1(qs,i,j+1,min,max); // post cond of the subsituition
				assert max > max0; // to ensure that the maximum updated
				assert min <= max;
				assert min <= min0;  
				}

				if(qs[i][j]<min) {
				assert Inv1(qs,i,j+1,qs[i][j],max);// pre cond of the subsituition
				min:=qs[i][j];
				assert Inv1(qs,i,j+1,min,max); // post cond of the subsituition
				assert min <= max;
				assert min < min0; // to ensure that the min updated
				}
			assert Inv1(qs,i,j+1,min,max);// pre cond of the subsituition
			j:=j+1;
			assert Inv1(qs,i,j,min,max); // post cond of the subsituition
	}
	// we here get out of the while .. so the invariant of the while must be correct so..--> this is an forward assert 
	assert Inv1(qs,i,j,min,max);

	
	assert Inv1(qs,i+1,0,min,max) &&  0 <= |qs|-(i+1) < |qs|-i0; // / pre cond of the down subsituition
	i:=i+1;
	assert Inv1(qs,i,0,min,max) &&  0 <= |qs|-i < |qs|-i0; // post cond of the up sub

	assert Inv1(qs,i,0,min,max) &&  0 <= |qs|-i < |qs|-i0; // pre cond of the down sub
	j:=0;
	assert Inv1(qs,i,j,min,max) &&  0 <= |qs|-i < |qs|-i0; // post cond of the up sub

	assert Inv1(qs,i,j,min,max) &&  0 <= |qs|-i < |qs|-i0; // the post condition of EE1 method
	
	}

predicate Inv1(qs: seq<seq<int>>, i: nat, j: nat, min: int, max: int)
{
	i <= |qs| &&
	(i < |qs| ==> j <= |qs[i]|) && min <= max &&
	(exists row: nat,column: nat :: ((row < i && column < |qs[row]|) || (row == i < |qs| && column < j)) && min == qs[row][column]) &&
	(exists row: nat,column: nat :: ((row < i && column < |qs[row]|) || (row == i < |qs| && column < j)) && max == qs[row][column]) &&
	(forall row: nat,column: nat :: (row < i && column < |qs[row]|) || (row == i < |qs| && column < j) ==> min <= qs[row][column] <= max)
}

