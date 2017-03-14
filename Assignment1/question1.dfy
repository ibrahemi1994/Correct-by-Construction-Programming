method Main() {
	var m: array2<int> := new int[5,5];
	m[0,0],m[0,1],m[0,2],m[0,3],m[0,4] :=  1, 3,-2, 7, 0;
	m[1,0],m[1,1],m[1,2],m[1,3],m[1,4] := -1,-2, 2,17,-5;
	m[2,0],m[2,1],m[2,2],m[2,3],m[2,4] :=  2, 2, 1,-4,-3;
	m[3,0],m[3,1],m[3,2],m[3,3],m[3,4] :=  0, 0, 1, 7,17;
	m[4,0],m[4,1],m[4,2],m[4,3],m[4,4] := -2, 8,-2, 2, 8;

	var sum := MatrixDiagonal(m,5,2);
	print sum;
	assert sum == 12 by {
		calc {
			MatrixDiagSum(m,5,2);
		==
			SumOnD(m,5,2,0,0,0);
		==
			SumOnD(m,5,2,0,1,0);
		==
			SumOnD(m,5,2,0,2,0);
		==
			SumOnD(m,5,2,0,3,m[0,2]);
		==
			SumOnD(m,5,2,0,4,m[0,2]);
		==
			SumOnD(m,5,2,0,5,m[0,2]);
		==
			SumOnD(m,5,2,1,0,m[0,2]);
		==
			SumOnD(m,5,2,1,1,m[0,2]);
		==
			SumOnD(m,5,2,1,2,m[0,2]);
		==
			SumOnD(m,5,2,1,3,m[0,2]);
		==
			SumOnD(m,5,2,1,4,m[0,2]+m[1,3]);
		==
			SumOnD(m,5,2,1,5,m[0,2]+m[1,3]);
		==
			SumOnD(m,5,2,2,0,m[0,2]+m[1,3]);
		==
			SumOnD(m,5,2,2,1,m[0,2]+m[1,3]+m[2,0]);
		==
			SumOnD(m,5,2,2,2,m[0,2]+m[1,3]+m[2,0]);
		==
			SumOnD(m,5,2,2,3,m[0,2]+m[1,3]+m[2,0]);
		==
			SumOnD(m,5,2,2,4,m[0,2]+m[1,3]+m[2,0]);
		==
			SumOnD(m,5,2,2,5,m[0,2]+m[1,3]+m[2,0]+m[2,4]);
		==
			SumOnD(m,5,2,3,0,m[0,2]+m[1,3]+m[2,0]+m[2,4]);
		==
			SumOnD(m,5,2,3,1,m[0,2]+m[1,3]+m[2,0]+m[2,4]);
		==
			SumOnD(m,5,2,3,2,m[0,2]+m[1,3]+m[2,0]+m[2,4]+m[3,1]);
		==
			SumOnD(m,5,2,3,3,m[0,2]+m[1,3]+m[2,0]+m[2,4]+m[3,1]);
		==
			SumOnD(m,5,2,3,4,m[0,2]+m[1,3]+m[2,0]+m[2,4]+m[3,1]);
		==
			SumOnD(m,5,2,3,5,m[0,2]+m[1,3]+m[2,0]+m[2,4]+m[3,1]);
		==
			SumOnD(m,5,2,4,0,m[0,2]+m[1,3]+m[2,0]+m[2,4]+m[3,1]);
		==
			SumOnD(m,5,2,4,1,m[0,2]+m[1,3]+m[2,0]+m[2,4]+m[3,1]);
		==
			SumOnD(m,5,2,4,2,m[0,2]+m[1,3]+m[2,0]+m[2,4]+m[3,1]);
		==
			SumOnD(m,5,2,4,3,m[0,2]+m[1,3]+m[2,0]+m[2,4]+m[3,1]+m[4,2]);
		==
			SumOnD(m,5,2,4,4,m[0,2]+m[1,3]+m[2,0]+m[2,4]+m[3,1]+m[4,2]);
		==
			SumOnD(m,5,2,4,5,m[0,2]+m[1,3]+m[2,0]+m[2,4]+m[3,1]+m[4,2]);
		==
			SumOnD(m,5,2,5,0,m[0,2]+m[1,3]+m[2,0]+m[2,4]+m[3,1]+m[4,2]);
		==
			m[0,2]+m[1,3]+m[2,0]+m[2,4]+m[3,1]+m[4,2];
		==
			-2+17+2-3+0-2;
		==
			12;
		}
	}
}

function MatrixDiagSum(m: array2<int>, N: nat, d: nat): int
	requires m != null && d < N == m.Length0 == m.Length1
	reads m
{
	SumOnD(m, N, d, 0, 0, 0)
} 

function SumOnD(m: array2<int>, N: nat, d: nat, i: nat, j: nat, sum: int): int
	requires m != null && d < N == m.Length0 == m.Length1 && i <= N && j <= N
	decreases N-i, N-j
	reads m
{
	if i == N then sum else
	if j == N then SumOnD(m, N, d, i+1, 0, sum) else
	if Abs(i-j) == d then SumOnD(m, N, d, i, j+1, sum+m[i,j]) else
	SumOnD(m, N, d, i, j+1, sum)
}

function method Abs(n: int): nat { if n>=0 then n else -n }

method MatrixDiagonal(m: array2<int>, N: nat, d: nat) returns (s: int)
	requires m != null && d < N == m.Length0 == m.Length1

	ensures s == MatrixDiagSum(m,N,d)
{
	/*
		The following implementation makes N*N checks of "Abs(i-j) == d".
		Re-implement without any use of "Abs" (make it a simple "function", not a "function method").
		The challenge is to compute the sum of the relevant elements from each row directly,
		skipping all irrelevant elements.
	*/
	s := 0;
	var i: nat := 0;
	var j: nat := 0;
	// Lemma2(m: array2<int>, jk:nat , N: nat, d: nat, i: nat, j: nat, s: int)
	while i != N
		invariant i <= N
		invariant m.Length1>0
		invariant MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,j,s)
		decreases N-i
	{
	assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,j,s);
	var j: nat := 0;	
	var tmpj:nat :=0;
 //	Lemma2(m,0,N,d,i,j,s);
	assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,j,s);
				if(d==0 ){
					//assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,i,s+m[i,i]);
					if(tmpj==0){
						if(j+1<N ){
								tmpj := j+1;
								assert tmpj <N;
								assert 0 <= tmpj <= N-1 < N  ;
								assert(i-tmpj>=0 ==> i-tmpj!=d || i-tmpj<0 ==> -i+tmpj !=d );
							//	Lemma2(m,1,N,d,i,N-1,s) ;
							}
					}
					j:=i;
				//	if(tmpj<N-1 && tmpj<m.Length1 ){
				//	tmpj := tmpj+1;
				//	}
				//	assert tmpj< N;
					//Lemma2(m,tmpj,N,d,i,j,s) ;

				//	Lemma2( m, tmpj, N, d, i, N-1, s) ;
					//assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,j,s+m[i,j]);
					s :=s+m[i,j];
					
				//	assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,j,s);
				}
				else{
					if(i-d >=0){
						Lemma2(m,tmpj,N,d,i,j,s) ;
						j:=i-d;
						assert j+1<m.Length1;
						///Lemma2(m,j+1,N,d,i,j,s) ;
				//	var tmpj :nat :=j-1
				//		Lemma2(m,0,N,d,i,j,s) ;
						s :=s+m[i,j];
						Lemma2(m,tmpj,N,d,i,j,s) ;
						if(i+d < N ){
						Lemma2(m,tmpj,N,d,i,j,s) ;
							j := i+d;
							Lemma2(m,j,N,d,i,j,s) ;
							s :=s+m[i,j];
						}
					}
					else{
						if(i+d<N){
							j:=i+d;
							Lemma2(m,tmpj,N,d,i,j,s) ;
							s :=s+m[i,j];
							if(j+1<N ){
								tmpj := j+1;
								assert tmpj <N;
								assert 0 <= tmpj <= N-1 < N  ;
								Lemma2(m,tmpj,N,d,i,N-1,s) ;
							}
						}
					}
				}		
				i := i+1;
			//assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,j,s);
	}
	assert s == MatrixDiagSum(m,N,d); //postcond
	assert !(i!=N); // loop guard 
}


method MatrixDiagonal'(m: array2<int>, N: nat, d: nat) returns (s: int)
	requires m != null && d < N == m.Length0 == m.Length1
	ensures s == MatrixDiagSum(m,N,d)
{
	s := 0;
	var i: nat := 0;
	while i != N
		invariant i <= N
		invariant MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,0,s)
		decreases N-i
	{
		var j: nat := 0;
		while j != N
			invariant j <= N
			invariant MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,j,s)
			decreases N-j
		{
			assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,j,s);
			if Abs(i-j) == d
			{
				assert m != null && d < N;
				assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,j,s);
				assert Abs(i-j) == d;
				assert i < N && j < N;
				// ==>
				assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,j+1,s+m[i,j]);
				s := s+m[i,j];
				assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,j+1,s);
			}
			else
			{
				assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,j,s);
				assert Abs(i-j) != d;
				assert i < N && j < N;
				// ==>
				assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,j+1,s);
			}
			assert MatrixDiagSum(m,N,d) == SumOnD(m,N,d,i,j+1,s);
			j := j+1;
		}
		i := i+1;
	}
}

lemma L1(m: array2<int>, N: nat, d: nat, i: nat, j: nat, s: int)
	// an irrelevant element a[i,j] (with "Abs(i-j) != d") can be skipped...

	requires m != null && d < N == m.Length0 == m.Length1
	requires i < N
	requires j < N
	requires Abs(i-j) != d 
	ensures SumOnD(m,N,d,i,j,s) == SumOnD(m,N,d,i,j+1,s)
{
	assert SumOnD(m,N,d,i,j,s) == SumOnD(m,N,d,i,j+1,s) ;
	
	/*by
	{
		assert i < N;
		assert j < N;
		assert d != Abs(i-j);
	};
	*/
}


lemma Lemma2(m: array2<int>, jk:nat , N: nat, d: nat, i: nat, j: nat, s: int)
	requires m != null && d < N == m.Length0 == m.Length1 
	requires N>0
	requires 0 <= jk < j < N   ||  0 <= jk == j < N
	requires i<=N 
	requires forall c :: 0 <=jk <=c < j  <m.Length0   ==>  (Abs(i-c)!=d) 
	ensures SumOnD(m,N,d,i,jk,s) == SumOnD(m,N,d,i,j,s)
	{
		var k:nat := jk;
		assert k>=0;
		while k!=j
		invariant j-k >=0
		invariant jk<=k<=j && ( ( i-k>=0 ==> i-k!=d || i-k<0 ==> -i+k !=d ) || (Abs(i-k)!=d)) &&(( i-jk>=0 ==> i-jk!=d || i-jk<0 ==> -i+jk !=d ) || (Abs(i-jk)!=d)) ==> SumOnD(m,N,d,i,jk,s) == SumOnD(m,N,d,i,k,s)
		decreases j-k 
		{
			k:=k+1;
		}
	}
	

	

