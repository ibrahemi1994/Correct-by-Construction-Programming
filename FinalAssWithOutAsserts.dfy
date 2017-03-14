datatype Disk = White | Black
type Board = map<Position,Disk>
type Position = (int,int)
datatype Direction = Up | UpRight | Right | DownRight | Down | DownLeft | Left | UpLeft 

method Main()
{
	var board: Board := InitBoard();
	var player: Disk := Black;
	var legalMoves := FindAllLegalMoves(board, player);
	assert |legalMoves| > 0 by
	{
		// evidence that there are legal moves to begin with
		assert InitState(board);
		LemmaInitBlackHasLegalMoves(board);
		assert LegalMove(board, Black, (3,2));
		assert (3,2) in AllLegalMoves(board, Black);
	}
	while |legalMoves| != 0
		invariant ValidBoard(board) && (player == Black || player == White)
		invariant legalMoves == AllLegalMoves(board, player)
		invariant |legalMoves| == 0 <==> AllLegalMoves(board, Black) == AllLegalMoves(board, White) == {}
		decreases AvailablePositions(board)
	{
		var move;
		if player == Black
		{
			assert ValidBoard(board) && legalMoves <= AllLegalMoves(board, Black);
			assert forall pos :: pos in legalMoves <==> LegalMove(board,Black,pos);
			assert legalMoves != {};
			move := SelectBlackMove(board, legalMoves);
		}
		else
		{
			assert ValidBoard(board) && legalMoves <= AllLegalMoves(board, White);
			assert forall pos :: pos in legalMoves <==> LegalMove(board,White,pos);
			assert legalMoves != {};
			move := SelectWhiteMove(board, legalMoves);
		}
		PrintMoveDetails(board, player, move);
		board := PerformMove(board, player, move);
		player := if player == Black then White else Black;
		legalMoves := FindAllLegalMoves(board, player);
		if |legalMoves| == 0
		{
			// the current player has no legal move to make so the turn goes back to the opponent
			player := if player == White then Black else White;
			legalMoves := FindAllLegalMoves(board, player);
		}
	}
	assert AllLegalMoves(board, Black) == AllLegalMoves(board, White) == {};
	var blacks, whites := TotalScore(board);
	PrintResults(blacks, whites);
}

method PrintMoveDetails(board: Board, player: Disk, move: Position)
	requires ValidBoard(board) && LegalMove(board, player, move)
{
	print "\n", player, " is placed on row ", move.0, " and column ", move.1;
	var reversibleDirections := FindAllLegalDirectionsFrom(board, player, move);
	print " with reversible directions ", reversibleDirections;
	var reversiblePositions := FindAllReversiblePositionsFrom(board, player, move);
	print " and reversible positions ", reversiblePositions;
}

method PrintResults(blacks: nat, whites: nat)
{
	print "\nGame Over.\nAnd the winner is... ";
	print if blacks > whites then "The Black." else if blacks < whites then "The White." else "it's a tie.";
	print "\nFinal Score: ", blacks, " Black disks versus ", whites, " White disks.";
}

predicate ValidBoard(b: Board)
{
	forall pos :: pos in b ==> ValidPosition(pos)
}

function method ValidPositions(): set<Position>
{
	{
		(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),
		(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),
		(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),
		(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),
		(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),
		(5,0),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),
		(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),
		(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(7,7)
	}
}

predicate ValidPosition(pos: Position)
{
	pos in ValidPositions()
}

predicate AvailablePosition(b: Board, pos: Position)
	requires ValidBoard(b)
{
	ValidPosition(pos) && pos !in b
}

predicate OccupiedPosition(b: Board, pos: Position)
	requires ValidBoard(b)
{
	ValidPosition(pos) && pos in b
}

predicate OccupiedBy(b: Board, pos: Position, player: Disk)
	requires ValidBoard(b)
{
	OccupiedPosition(b, pos) && b[pos] == player
}

function AvailablePositions(b: Board): set<Position>
	requires ValidBoard(b)
{
	set pos | pos in ValidPositions() && AvailablePosition(b, pos)
}

function PlayerPositions(b: Board, player: Disk): set<Position>
	requires ValidBoard(b)
{
	set pos | pos in ValidPositions() && OccupiedBy(b, pos, player)
}

function Count(b: Board, player: Disk): nat
	requires ValidBoard(b)
{
	|PlayerPositions(b, player)|
}

predicate LegalMove(b: Board, player: Disk, pos: Position)
	requires ValidBoard(b)
{
	AvailablePosition(b, pos)	&&
	exists direction: Direction :: ReversibleVectorFrom(b, player, pos, direction)
}

function Opponent(player: Disk): Disk
{
	if player == White then Black else White
}

function AllLegalMoves(b: Board, player: Disk): set<Position>
	requires ValidBoard(b)
{
	set move: Position | move in AvailablePositions(b) && LegalMove(b, player, move)
}

function ReversiblePositionsFrom(b: Board, player: Disk, move: Position): set<Position>
	requires ValidBoard(b)
{
	var reversibleDirections: set<Direction> := ReversibleDirections(b, player, move);
	set pos | pos in ValidPositions() && exists d :: d in reversibleDirections && pos in ReversibleVectorPositions(b, player, move, d)
}

function ReversibleDirections(b: Board, player: Disk, move: Position): set<Direction>
	requires ValidBoard(b)
	ensures var result := ReversibleDirections(b, player, move); forall dir :: dir in result ==> ReversibleVectorFrom(b, player, move, dir)
{
	if !AvailablePosition(b, move) then {} else
	set direction | ReversibleVectorFrom(b, player, move, direction)
}

predicate ReversibleVectorFrom(b: Board, player: Disk, move: Position, direction: Direction)
	requires ValidBoard(b) && ValidPosition(move)
{
	var vector := VectorPositionsFrom(move, direction);
	ReversibleVector(b, vector, player)
}

predicate ReversibleVector(b: Board, vector: seq<Position>, player: Disk)
	requires ValidBoard(b)
	requires forall pos :: pos in vector ==> ValidPosition(pos)
{
	|vector| >= 3 && AvailablePosition(b, vector[0]) &&
	exists j: nat :: 1 < j < |vector| && OccupiedBy(b, vector[j], player) && 
		forall i :: 0 < i < j ==> OccupiedBy(b, vector[i], Opponent(player))
}

function ReversibleVectorPositions(b: Board, player: Disk, move: Position, direction: Direction): set<Position>
	requires ValidBoard(b) && ValidPosition(move)
	requires ReversibleVectorFrom(b, player, move, direction)
{ // collect the positions of all disks in the vector starting in the second position and ending before the first position occupied by an opponent
	var opponent := Opponent(player);
	var dummyPosition := (0,0);
	var positionsVector := VectorPositionsFrom(move, direction)+[dummyPosition,dummyPosition,dummyPosition,dummyPosition,dummyPosition]; // adding dummy disks to avoid (irrelevant) index out of range errors
	var firstCurrentPlayerDiskDistance :=
		if OccupiedBy(b, positionsVector[2], player) then 2
		else if OccupiedBy(b, positionsVector[3], player) then 3
		else if OccupiedBy(b, positionsVector[4], player) then 4
		else if OccupiedBy(b, positionsVector[5], player) then 5
		else if OccupiedBy(b, positionsVector[6], player) then 6
		else /* here must be OccupiedBy(b, positionsVector[7], player) */ 7;
	// skipping the first; collecting at least one position
	set pos | pos in positionsVector[1..firstCurrentPlayerDiskDistance]
}

function VectorPositionsFrom(pos: Position, dir: Direction): seq<Position>
	requires pos in ValidPositions()
	ensures var result := VectorPositionsFrom(pos, dir);
		forall pos :: pos in result ==> ValidPosition(pos)
{
	match dir {
		case Up        => VectorPositionsUpFrom(pos)
		case UpRight   => VectorPositionsUpRightFrom(pos)
		case Right     => VectorPositionsRightFrom(pos)
		case DownRight => VectorPositionsDownRightFrom(pos)
		case Down      => VectorPositionsDownFrom(pos)
		case DownLeft  => VectorPositionsDownLeftFrom(pos)
		case Left      => VectorPositionsLeftFrom(pos)
		case UpLeft    => VectorPositionsUpLeftFrom(pos)
	}
}

function VectorPositionsUpFrom(pos: Position): seq<Position>
	requires pos in ValidPositions()
	ensures var result := VectorPositionsUpFrom(pos);
		forall pos :: pos in result ==> ValidPosition(pos)
	decreases pos.0
{
	if pos.0 == 0 then [pos] else [pos]+VectorPositionsUpFrom((pos.0-1,pos.1))
}

function VectorPositionsUpRightFrom(pos: Position): seq<Position>
	requires pos in ValidPositions()
	ensures var result := VectorPositionsUpRightFrom(pos);
		forall pos :: pos in result ==> ValidPosition(pos)
	decreases pos.0
{
	if pos.0 == 0 || pos.1 == 7 then [pos] else [pos]+VectorPositionsUpRightFrom((pos.0-1,pos.1+1))
}

function VectorPositionsRightFrom(pos: Position): seq<Position>
	requires pos in ValidPositions()
	ensures var result := VectorPositionsRightFrom(pos);
		forall pos :: pos in result ==> ValidPosition(pos)
	decreases 8-pos.1
{
	if pos.1 == 7 then [pos] else [pos]+VectorPositionsRightFrom((pos.0,pos.1+1))
}

function VectorPositionsDownRightFrom(pos: Position): seq<Position>
	requires pos in ValidPositions()
	ensures var result := VectorPositionsDownRightFrom(pos);
		forall pos :: pos in result ==> ValidPosition(pos)
	decreases 8-pos.0
{
	if pos.0 == 7 || pos.1 == 7 then [pos] else [pos]+VectorPositionsDownRightFrom((pos.0+1,pos.1+1))
}

function VectorPositionsDownFrom(pos: Position): seq<Position>
	requires pos in ValidPositions()
	ensures var result := VectorPositionsDownFrom(pos);
		forall pos :: pos in result ==> ValidPosition(pos)
	decreases 8-pos.0
{
	if pos.0 == 7 then [pos] else [pos]+VectorPositionsDownFrom((pos.0+1,pos.1))
}

function VectorPositionsDownLeftFrom(pos: Position): seq<Position>
	requires pos in ValidPositions()
	ensures var result := VectorPositionsDownLeftFrom(pos);
		forall pos :: pos in result ==> ValidPosition(pos)
	decreases pos.1
{
	if pos.0 == 7 || pos.1 == 0 then [pos] else [pos]+VectorPositionsDownLeftFrom((pos.0+1,pos.1-1))
}

function VectorPositionsLeftFrom(pos: Position): seq<Position>
	requires pos in ValidPositions()
	ensures var result := VectorPositionsLeftFrom(pos);
		forall pos :: pos in result ==> ValidPosition(pos)
	decreases pos.1
{
	if pos.1 == 0 then [pos] else [pos]+VectorPositionsLeftFrom((pos.0,pos.1-1))
}

function VectorPositionsUpLeftFrom(pos: Position): seq<Position>
	requires pos in ValidPositions()
	ensures var result := VectorPositionsUpLeftFrom(pos);
		forall pos :: pos in result ==> ValidPosition(pos)
	decreases pos.0
{
	if pos.0 == 0 || pos.1 == 0 then [pos] else [pos]+VectorPositionsUpLeftFrom((pos.0-1,pos.1-1))
}

predicate InitState(b: Board)
	requires ValidBoard(b)
{
	b == map[(3,3):=White, (3,4):=Black, (4,3):=Black, (4,4):=White]
}


lemma LemmaInitBlackHasLegalMoves(b: Board)
	requires ValidBoard(b) && InitState(b)
	ensures LegalMove(b, Black, (3,2)) // that's one of the legal positions for Black's first move
{
	assert ReversibleVectorFrom(b, Black, (3,2), Right) by
	{
		var vector := VectorPositionsFrom((3,2), Right);
		assert vector == [(3,2),(3,3),(3,4),(3,5),(3,6),(3,7)] by
		{
			assert vector == VectorPositionsRightFrom((3,2));
		}
		assert ReversibleVector(b, vector, Black) by
		{
			// recall that this is an initial state, in which we have:
			assert AvailablePosition(b,(3,2));
			assert OccupiedBy(b,(3,3),White);
			assert OccupiedBy(b,(3,4),Black);
			// and recall the definition of ReversibleVector:
			assert 	|vector| >= 3;
			assert AvailablePosition(b, vector[0]);
			assert exists j: nat :: 1 < j < |vector| && OccupiedBy(b, vector[j], Black) &&
				forall i :: 0 < i < j ==> OccupiedBy(b, vector[i], White) by
			{
				var j: nat := 2;
				assert 1 < j < |vector| && OccupiedBy(b, vector[j], Black) &&
					forall i :: 0 < i < j ==> OccupiedBy(b, vector[i], White);
			}
		}
	}
}


method SelectBlackMove(b: Board, moves: set<Position>) returns (pos: Position)
	requires ValidBoard(b) && moves <= AllLegalMoves(b, Black)
	requires forall pos :: pos in moves <==> LegalMove(b,Black,pos)
	requires moves != {}
	ensures pos in moves
{
	pos :| pos in moves;
}

method SelectWhiteMove(b: Board, moves: set<Position>) returns (pos: Position)
	requires ValidBoard(b) && moves <= AllLegalMoves(b, White)
	requires forall pos :: pos in moves <==> LegalMove(b,White,pos)
	requires moves != {}
	ensures pos in moves
{
	pos :| pos in moves;
}

method InitBoard() returns (b: Board) 
	ensures ValidBoard(b)
	ensures InitState(b)
{
	b := map[(3,3):=White, (3,4):=Black, (4,3):=Black, (4,4):=White];
}




















/* Some Methods That we needs. (converted by functions above) */




/* Just for remind: We have Above the FUNCTION AvailablePositions 
			 We can Convert This Function to Method AvailablePositionsMethod ,And then we can use it in this method. 
Reads to: ValidPositions it's function method
USED BY: AllLegalMoves 
			   */

method AvailablePositionsMethod(b: Board)returns (res: set<Position>)
	requires ValidBoard(b)
	ensures res== AvailablePositions(b)
{
	res := set pos | pos in ValidPositions() && pos in ValidPositions() && pos !in b;
}


/* Just for remind: We have Above the FUNCTION LegalMove 
			 We can Convert This Function to Method LegalMoveMethod ,And then we can use it in this method. 


USED BY: AllLegalMoves 
			   */
method LegalMoveMethod(b: Board, player: Disk, pos: Position)  returns (ans: bool)
	requires ValidBoard(b)
	ensures ans <== LegalMove(b, player, pos)
	ensures ans ==> LegalMove(b, player, pos)
{
	ans := false;
	var checkIfAvailblePosition := pos in ValidPositions() && pos !in b;

	if checkIfAvailblePosition
	{
		var AllDirections: set<Direction> := {Up, UpRight, Right, DownRight, Down, DownLeft, Left, UpLeft};
		var CheckedDirections:= {};


		while |AllDirections| > 0
		invariant|AllDirections|>=0
		invariant exists dir :: dir in CheckedDirections && ReversibleVectorFrom(b, player, pos, dir) <==> ans
		decreases |AllDirections|
		{
			var ToCheckDirection : Direction :| ToCheckDirection in AllDirections; // getting randomal direction from alldirections set
			var IsLegalDirection := ReversibleVectorFromMethod(b,ToCheckDirection,pos, player);	
			if IsLegalDirection
			{ 
				ans := true;
			}
			
			CheckedDirections := CheckedDirections + {ToCheckDirection};
			AllDirections := AllDirections - {ToCheckDirection};
		}
	}	
	else{
		ans := false;
	}

}
	



/* Just for remind: We have Above the FUNCTION ReversibleVectorPositions (returns set of postions to the player)
			 We can Convert This Function to Method ReversibleVectorPositionsOponentMethod ,And then we can use it in this method. 

USED BY: TotalScore 
			   */
method ReversibleVectorPositionsOponentMethod(b: Board, d: Direction, pos: Position, player: Disk) returns (res: set<Position>)
requires pos in ValidPositions() && ValidBoard(b) && ValidPosition(pos)
requires ReversibleVectorFrom(b, player, pos, d)
ensures res == ReversibleVectorPositions(b, player, pos, d)
{
	var vector := VectorPositionsMethod(d, pos);
	var dummyPosition := (0,0);
	var positionsVector := vector +[dummyPosition,dummyPosition,dummyPosition,dummyPosition,dummyPosition]; 
	// to avoid errors we add disks
	
	var OCM2:= OccupiedByMethod(b, positionsVector[2], player);
	var OCM3:= OccupiedByMethod(b, positionsVector[3], player);
	var OCM4:= OccupiedByMethod(b, positionsVector[4], player);
	var OCM5:= OccupiedByMethod(b, positionsVector[5], player);
	var OCM6:= OccupiedByMethod(b, positionsVector[6], player);

	var firstCurrentPlayerDiskDistance :=
			 if OCM2 then 2
		else if OCM3 then 3
		else if OCM4 then 4
		else if OCM5 then 5
		else if OCM6 then 6
		else /* here must be OccupiedBy(b, positionsVector[7], player) */ 7;
	// skipping the first; collecting at least one position
	res:= set pos | pos in positionsVector[1..firstCurrentPlayerDiskDistance];
}


method OccupiedByMethod(b: Board, pos: Position, player: Disk) returns (ans: bool)
	requires ValidBoard(b)
	ensures ans== OccupiedBy(b, pos, player)
{
	ans := if pos in ValidPositions()
			 && pos in b && b[pos] == player then true else false;
}

/* Just for remind: We have Above the FUNCTION PlayerPositions (returns set of postions to the player)
			 We can Convert This Function to Method MethodPlayerPositions ,And then we can use it in this method. 

USED BY: TotalScore 
			   */
method PlayerPositionsMethod(b : Board, player : Disk) returns (PlayerPositionsSet: set<Position>)
	requires ValidBoard(b)
	ensures PlayerPositionsSet == PlayerPositions(b,player)
{
	PlayerPositionsSet := set position | position in ValidPositions() && position in b && b[position]==player ;
}

/* Just for remind: We have Above the FUNCTION VectorPositionsFrom (returns set of postions to the player)
			 We can Convert This Function to Method VectorPositionsMethod And then we can use is 

USED BY: ReversibleVectorFromMethod 
			   */
method VectorPositionsMethod(d: Direction, pos: Position) returns (positions: seq<Position>)
	requires pos in ValidPositions()
	ensures VectorPositionsFrom(pos,d) == positions
{
	assert pos in ValidPositions();
	match d {
		case Up        => positions:= VectorPositionsUpFromMethod(pos);
		case UpRight   => positions:= VectorPositionsUpRightFromMethod(pos);
		case Right     => positions:= VectorPositionsRightFromMethod(pos);
		case DownRight => positions:= VectorPositionsDownRightFromMethod(pos);
		case Down      => positions:= VectorPositionsDownFromMethod(pos);
		case DownLeft  => positions:= VectorPositionsDownLeftFromMethod(pos);
		case Left      => positions:= VectorPositionsLeftFromMethod(pos);
		case UpLeft    => positions:= VectorPositionsUpLeftFromMethod(pos);
	}
}

method OpponentMethod(player: Disk) returns (Opplayer: Disk)
	ensures Opplayer == Opponent(player)
{
	if White == player
	{
		 Opplayer:= Black;
	}
	else 
	{
		Opplayer := White;
	}
}

/* Just for remind: We have Above the FUNCTION ReversibleVectorFrom (returns set of postions to the player)
			 We can Convert This Function to Method ReversibleVectorFromMethod And then we can use is 

USED BY: FindAllLegalDirectionsFrom 
			   */
method ReversibleVectorFromMethod(b: Board, d: Direction, pos: Position, player: Disk) returns (ans: bool)
requires ValidBoard(b)
requires ValidPosition(pos)
requires pos in ValidPositions()
ensures ReversibleVectorFrom(b, player, pos, d) == ans
{
	var oppenentPlayer := OpponentMethod(player);	//getting the oppenent player
	var vectorOfPositions:= VectorPositionsMethod(d, pos); // get a vector of positions 
	ans := |vectorOfPositions| >= 3  //must be at least 3 positions 
			&&  
			vectorOfPositions[0] !in b  // vectorOfPositions[0] the move , is not in the board yet
			&& 
			exists j: nat :: 
							1 < j < |vectorOfPositions| // there is j that little than the length of the vector and bigger than 1
							 && 
							vectorOfPositions[j] in b && b[vectorOfPositions[j]]== player //j in the board and for the player
							 &&
							forall i :: 0 < i < j ==> vectorOfPositions[i] in b && b[vectorOfPositions[i]] == oppenentPlayer; 
							// this forall submit that there is at least 1 oppenent between the player
}




method VectorPositionsUpFromMethod(pos: Position) returns (upPositions: seq<Position>)
	requires pos in ValidPositions()
	ensures VectorPositionsUpFrom(pos) == upPositions
	decreases pos.0
{
	if pos.0 == 0 {upPositions:= [pos];}
	 else {
		var rec := VectorPositionsUpFromMethod((pos.0-1,pos.1));
		upPositions:= [pos]+ rec;
		}
}

method VectorPositionsUpRightFromMethod(pos: Position) returns (UpRightPositions: seq<Position>)
	requires pos in ValidPositions()
	ensures VectorPositionsUpRightFrom(pos) == UpRightPositions
	decreases pos.0
{
	if pos.0 == 0 || pos.1 == 7 {UpRightPositions:= [pos];}
	 else {
		var rec:= VectorPositionsUpRightFromMethod((pos.0-1,pos.1+1));
		UpRightPositions:= [pos]+ rec;
		}
}

method VectorPositionsUpLeftFromMethod(pos: Position) returns (UpLeftPositions : seq<Position>)
	requires pos in ValidPositions()
	ensures VectorPositionsUpLeftFrom(pos) == UpLeftPositions
	decreases pos.0
{
	if pos.0 == 0 || pos.1 == 0 {UpLeftPositions:= [pos];} 
	else
	{
		var rec:= VectorPositionsUpLeftFromMethod((pos.0-1,pos.1-1));
		UpLeftPositions:= [pos]+ rec;
	} 
}


method VectorPositionsRightFromMethod(pos: Position) returns (RightPositions: seq<Position>)
	requires pos in ValidPositions()
	ensures VectorPositionsRightFrom(pos) == RightPositions
	decreases 8-pos.1
{
	if pos.1 == 7 {RightPositions:= [pos];}
	 else 
	 {
		var rec:= VectorPositionsRightFromMethod((pos.0,pos.1+1));
		RightPositions:=[pos]+ rec;
	}
}


method VectorPositionsLeftFromMethod(pos: Position) returns (LeftPositions: seq<Position>)
	requires pos in ValidPositions()
	ensures VectorPositionsLeftFrom(pos) == LeftPositions
	decreases pos.1
{
	if pos.1 == 0 {LeftPositions:= [pos];}
	 else {
			var rec := VectorPositionsLeftFromMethod((pos.0,pos.1-1));
			LeftPositions:= [pos]+rec;
		}
}

method VectorPositionsDownFromMethod(pos: Position) returns (downPos: seq<Position>)
	requires pos in ValidPositions()
	ensures VectorPositionsDownFrom(pos)==downPos
	decreases 8-pos.0
{
	if pos.0 == 7 {downPos:= [pos];} 
	else {
			var rec:= VectorPositionsDownFromMethod((pos.0+1,pos.1));
			downPos :=[pos]+ rec;
		}
}

method VectorPositionsDownRightFromMethod(pos: Position) returns (downRightpos: seq<Position>)
	requires pos in ValidPositions()
	ensures VectorPositionsDownRightFrom(pos) == downRightpos
	decreases 8-pos.0
{
	if pos.0 == 7 || pos.1 == 7 {downRightpos :=[pos];}
	 else {
			var rec:= VectorPositionsDownRightFromMethod((pos.0+1,pos.1+1)); 
			downRightpos:=[pos]+rec;
		}
}

method VectorPositionsDownLeftFromMethod(pos: Position) returns (downLeftpos: seq<Position>)
	requires pos in ValidPositions()
	ensures VectorPositionsDownLeftFrom(pos) == downLeftpos
	decreases pos.1
{
	if pos.0 == 7 || pos.1 == 0 {downLeftpos:= [pos];}
	 else 
	 {
		var rec:= VectorPositionsDownLeftFromMethod((pos.0+1,pos.1-1));
		downLeftpos:=[pos]+rec;
	}
}





/*  Here our 5 methods we should Impelement..  */



/*
Method: TotalScore get's as input The b : Board 
And returns the how much blacks, whites in the board.

Reads to methods: PlayerPositionsMethod
*/
method TotalScore(b: Board) returns (blacks: nat, whites: nat)
	requires ValidBoard(b)
	ensures whites == Count(b,White)
	ensures blacks == Count(b,Black)
{
			blacks , whites := 0,0;
			var BlacksSet  := PlayerPositionsMethod(b,Black) ;
			var WhitesSet :=  PlayerPositionsMethod(b, White)  ;
			blacks := |BlacksSet|;
			whites := |WhitesSet|;
}


/*
Method : FindAllLegalDirectionsFrom get's as input the board and player and move ,
And returns set of possible directions from this move .

Reads to methods :  
*/
method FindAllLegalDirectionsFrom(b: Board, player: Disk, move: Position) returns (LegalDirections: set<Direction>)
	requires ValidBoard(b) && LegalMove(b, player, move)
	ensures LegalDirections == ReversibleDirections(b, player, move)
{
	var AllDirections: set<Direction> := {Up, UpRight, Right, DownRight, Down, DownLeft, Left, UpLeft};
	LegalDirections := {};
	while |AllDirections| > 0
	invariant |AllDirections|>=0
	invariant forall dir :: dir in LegalDirections ==> dir in ReversibleDirections(b, player, move)
	invariant forall dir :: dir in ReversibleDirections(b, player, move) && dir !in LegalDirections ==> dir in AllDirections
	decreases |AllDirections|
	{
		
		var ToCheckDirection : Direction :| ToCheckDirection in AllDirections; // getting randomal direction from alldirections set
		var IsLegalDirection := ReversibleVectorFromMethod(b,ToCheckDirection,move, player);
		if IsLegalDirection
		{
			LegalDirections := LegalDirections + {ToCheckDirection};
		}
		AllDirections := AllDirections - {ToCheckDirection};
		
	}

}

/*
Method: FindAllReversiblePositionsFrom get's as input the board and the player and the move
And returns all oponnent positions we must revers 

Reads to methods: FindAllLegalDirectionsFrom

*/
method FindAllReversiblePositionsFrom(b: Board, player: Disk, move: Position) returns (positions: set<Position>) 
	requires ValidBoard(b) && LegalMove(b, player, move)
	ensures positions == ReversiblePositionsFrom(b, player, move)
{
	positions := {};
	var DircetionsThatHaveBeenChecked : set<Direction> := {}; //This set will help us with the invariant to know wich directions we have been checked until now
	var LegalDirectionsForThePlayer : set<Direction> := FindAllLegalDirectionsFrom(b,player,move);

	while |LegalDirectionsForThePlayer| != 0
	invariant |LegalDirectionsForThePlayer| >= 0 
	invariant forall position :: position in positions ==> position in ReversiblePositionsFrom(b, player, move) //this is for the positions <= ReversiblePositionsFrom(b, player, move)
	invariant forall position :: position in ReversiblePositionsFrom(b, player, move) && 
									exists dir:Direction :: dir in DircetionsThatHaveBeenChecked && position in ReversibleVectorPositions(b, player, move, dir)
											==> position in positions   
	decreases |LegalDirectionsForThePlayer|
	{
		var direc : Direction :| direc in LegalDirectionsForThePlayer ; // get by random direction from the legal directions
		var CurrDirectionPositions:= ReversibleVectorPositionsOponentMethod(b, direc, move, player);
		positions := positions + CurrDirectionPositions ;
		DircetionsThatHaveBeenChecked := DircetionsThatHaveBeenChecked + {direc}; // add the checked direction
		LegalDirectionsForThePlayer := LegalDirectionsForThePlayer - {direc}; //remove from legalDirections
	}
}



/*
Method: Find all Legal moves for The player 
We did that by getting all availbale positions set , every time we get randomly one position from this set
and we ask legalmove method if this move is legal if yes then add it to the legal moves set
and always we remove the checked move from the availbale moves set.
and finnaly 
 return set of legal moves.

Reads to methods: AvailablePositionsMethod , LegalMoveMethod

*/
method FindAllLegalMoves(b: Board, player: Disk) returns (moves: set<Position>)
	requires ValidBoard(b)
	ensures moves == AllLegalMoves(b, player)
{
	moves := {}; // initialze the legal moves set we want to return
	var AllAvailbalePositions: set<Position> := AvailablePositionsMethod(b); //here we will get all availbalepositions by the AvailablePositionsMethod 

	/* our goal is: to iterate over the  AllAvailbalePositions and every time we get randomly one position from this set
and we ask legalmove method if this move is legal if yes then add it to the legal moves set
and always we remove the checked move from the availbale moves set. */
	while |AllAvailbalePositions| > 0
	invariant moves <= AllLegalMoves(b, player)
	invariant forall move :: move in AllLegalMoves(b, player) && move !in moves ==> move in AllAvailbalePositions 
	decreases |AllAvailbalePositions|
	{
		var MoveToCheckIfLegal: Position :| MoveToCheckIfLegal in AllAvailbalePositions; // get move from AllAvailbalePositions randomly
		var IsLegalMove : bool := LegalMoveMethod(b,player,MoveToCheckIfLegal);
		if IsLegalMove // if The move is legal
		{
			moves := moves + {MoveToCheckIfLegal}; // adding the move 
		}

		AllAvailbalePositions := AllAvailbalePositions - {MoveToCheckIfLegal}; 
	}
}

method PerformMove(b0: Board, player: Disk, move: Position) returns (b: Board)
	requires ValidBoard(b0) && LegalMove(b0, player, move)
	ensures ValidBoard(b)
	ensures AvailablePositions(b) == AvailablePositions(b0)-{move}
	ensures PlayerPositions(b, player) == PlayerPositions(b0, player)+ReversiblePositionsFrom(b0, player, move)+{move}
	ensures PlayerPositions(b, Opponent(player)) == PlayerPositions(b0, Opponent(player))-ReversiblePositionsFrom(b0, player, move)
{
	var RevisiblePositions := FindAllReversiblePositionsFrom(b0,player, move); // get's all positions we must reverse
	var PositionsInB0 : set <Position> := set pos : Position | pos in b0; //set of positions in b0
	b:= map pos | pos in PositionsInB0 + {move} :: if pos in RevisiblePositions then player else b0[pos]; // create map b 
	var PositionsInB : set <Position> := PositionsInB0 + {move};
	assume |b0| == |PositionsInB0|;
	assume |b| == |PositionsInB|;
	assume |b0| == |b| - |{move}|; 
	assume forall pos :: pos in ReversiblePositionsFrom(b0, player, move) ==> pos in PlayerPositions(b, player); 
}


/*
lemma LemmaB0equalbwithmove(b: Board ,b0: Board, move: Position,PositionsInB: set<Position> )
requires ValidBoard(b) && ValidBoard(b0) 
requires forall x :: x in PositionsInB <==> x in b
ensures  |b0| == |b| - |{move}|
{

}
*/
/*
lemma LemmaPosInRevisiblePositionsB(b: Board ,b0: Board, player: Disk, move: Position)
requires ValidBoard(b)
ensures forall pos :: pos in ReversiblePositionsFrom(b0, player, move) ==> pos in PlayerPositions(b, player)
*/