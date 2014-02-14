#include "pisqpipe.h"
#include "board.h"

const int TRUE = 1;
const int FALSE = 0;
const int UNKNOWN = -1;

Node nodeBase[MAX_NODE_IN_MEM];
int totalNode;
PtrNode root;

int left_cur,right_cur,top_cur,down_cur; // current board rect
int left_outer,right_outer,top_outer,down_outer; // outer board rect

bool ResourceAvailable()
{
	return totalNode < MAX_NODE_IN_MEM - width * height;
}
PtrNode GetOneNode()
{
	if(totalNode<MAX_NODE_IN_MEM)
	{
		PtrNode node = nodeBase + totalNode;
		++totalNode;
		//ptrNode->value = UNKNOWN; // 0:false 1:true -1:unknown
		//proof,disproof; // num of unknow node
		//PtrNode children[MAX_NUM_CHILDREN];
		//numOfChildren;
		//ptrNode->type = OR; // and or
		node->expanded =false;
		node->evaluated = false;
		//int board[MAX_BOARD][MAX_BOARD];
		node->parent = 0;
		return node;
	}
	return 0;
}
bool InBoard(int x,int y)
{
	return x >= 0 && y >= 0 && x < width && y < height;
}
void PutAStone(PtrNode node)
{
	if(InBoard(node->x,node->y))
	{
		board[node->x][node->y] = node->type == OR ? PLAYER2:PLAYER1;
	}
}
void RemoveAStone(PtrNode node)
{
	if(InBoard(node->x,node->y))
	{
		board[node->x][node->y] = 0;
	}
}
int NumOfStoneInDir(int dir ,int x , int y , int player)
{
	int num = 0;

	while(InBoard(x,y) && board[x][y] == player)
	{
		++ num;
		x += dx[dir];
		y += dy[dir];
	}
	return num;
}
bool FormAFive(int x, int y,int player)
{
	for ( int i = 0; i < 8 ; ++ i )
	{
		if(NumOfStoneInDir(i,x,y,player) >= 5)
		{
			return true;
		}
	}
	return false;
}
bool HasFiveInARow(int player)
{
	for ( int x = 0 ; x < width; ++x)
	{
		for ( int y = 0 ; y < height; ++ y )
		{
			if(board[x][y] == player && FormAFive(x,y,player))
			{
				return true;
			}
		}
	}
	return false;
}
bool IsWinNode()
{
	return HasFiveInARow(PLAYER1);
}
bool IsLoseNode()
{
	return HasFiveInARow(PLAYER2);
}

bool IsBoardFull(PtrNode node)
{
	return node->moves == height * width;
}
bool IsTieNode(PtrNode node)
{
	return IsBoardFull(node);
}
void Evaluate(PtrNode node)
{
	if(IsWinNode())
	{
		node->value = TRUE;
	}
	else if ( IsLoseNode() || IsTieNode(node))
	{
		node->value = FALSE;
	}
	else
	{
		node->value = UNKNOWN;
	}
	node->evaluated = true;
}
int SumChildrenProof(PtrNode node)
{
	int sum = 0;

	for ( int i = 0 ; i < node->numOfChildren; ++ i)
	{
		sum += node->children[i]->proof;
	}

	return sum;
}
int SumChildrenDisproof(PtrNode node)
{
	int sum = 0;

	for ( int i = 0 ; i < node->numOfChildren; ++ i)
	{
		sum += node->children[i]->disproof;
	}

	return sum;
}
int MinChildrenProof(PtrNode node)
{
	int min = INF;

	for ( int i = 0 ; i < node->numOfChildren; ++ i)
	{
		if(node->children[i]->proof < min)
		{
			min = node->children[i]->proof;
		}
	}

	return min;
}
int MinChildrenDisproof(PtrNode node)
{
	int min = INF;

	for ( int i = 0 ; i < node->numOfChildren; ++ i)
	{
		if(node->children[i]->disproof < min)
		{
			min = node->children[i]->disproof;
		}
	}

	return min;
}
void SetProofAndDisproofNumbers(PtrNode node)
{
	if(node->expanded)
	{
		if(node->type == AND)
		{
			node->proof = SumChildrenProof(node);
			node->disproof = MinChildrenDisproof(node);
		}
		else if (node->type = OR)
		{
			node->proof = MinChildrenProof(node);
			node->disproof = SumChildrenDisproof(node);
		}
	}
	else if ( node->evaluated)
	{
		if (node->value == FALSE)
		{
			node->proof = INF;
			node->disproof = 0;
		}
		else if (node->value == TRUE)
		{
			node->proof=0;
			node->disproof= INF;
		}
		else if ( node->value == UNKNOWN)
		{
			//node->proof=1 + ( node->moves - root->moves ) / 2;
			//node->disproof=1 + ( node->moves - root->moves ) / 2;
			//node->proof=1 + ( node->moves - root->moves ) * ( node->moves - root->moves );
			//node->disproof=1 + ( node->moves - root->moves ) * ( node->moves - root->moves );
			node->proof=1;
			node->disproof=1;
			//node->proof = 1 + ( node->moves - root->moves ) / 2;
			//node->disproof = 1 + ( node->moves - root->moves ) / 2;
		}
	}
	else
	{
		node->proof = 1 + ( node->moves - root->moves ) / 2;
		node->disproof = 1 + ( node->moves - root->moves ) / 2;
	}
}

PtrNode SelectMostProving(PtrNode node)
{
	while(node->expanded)
	{
		int i = 0;
		if(node->type == OR)
		{
			while(node->children[i]->proof != node->proof)
			{
				++i ;
			}
		}
		else if (node->type == AND)
		{
			while(node->children[i]->disproof != node->disproof)
			{
				++i ;
			}
		}
		node = node->children[i];
		PutAStone(node);
	}
	return node;
}

void AddOneChild(PtrNode node , int x ,int y )
{
	PtrNode child = GetOneNode();

	child->parent = node;
	child->type = node->type == AND ? OR : AND; // and or
	child->x = x;
	child->y = y;

	//for ( int xx = 0 ; xx < width;++xx)
	//{
	//	for ( int yy = 0 ; yy < height; ++ yy)
	//	{
	//		child->board[xx][yy] = node->board[xx][yy];
	//	}
	//}

	//child->board[x][y] = node->type == OR ? PLAYER1:PLAYER2;

	node->children[node->numOfChildren] = child;
	++node->numOfChildren;

	child->moves = node->moves + 1;
}
int min(int a,int b)
{
	if(a<b)
	{
		return a;
	}
	return b;
}
int max(int a,int b)
{
	if(a>b)
	{
		return a;
	}
	return b;
}
void FindCurrentBoardRect()
{
	left_cur = width - 1;
	right_cur = 0;
	top_cur = height - 1;
	down_cur = 0;
	for ( int x = 0 ; x < width; ++x)
	{
		for ( int y = 0 ; y < height; ++ y)
		{
			if(board[x][y] != 0)
			{
				left_cur = min(left_cur,x);
				right_cur = max(top_cur,x);
				top_cur = min(top_cur,y);
				down_cur = max(down_cur,y);
			}
		}
	}
	left_outer = left_cur - OUTER;
	right_outer = right_cur + OUTER;
	top_outer = top_cur - OUTER;
	down_outer = down_cur + OUTER;

	left_outer = max(0,left_outer);
	right_outer = min(width-1,right_outer);
	top_outer = max(0,top_outer);
	down_outer = min(height-1,down_outer);
}
void GenerateAllChildren(PtrNode node)
{
	FindCurrentBoardRect();
	node->numOfChildren = 0;
	for ( int x = left_outer ; x <= right_outer; ++x)
	{
		for ( int y = top_outer ; y <= down_outer; ++ y)
		{
			if(board[x][y] == 0)
			{
				AddOneChild(node,x,y);
			}
		}
	}
}
PtrNode UpdateAncestors(PtrNode node)
{
	PtrNode previousNode;
	bool changed = true;
	int oldProof;
	int oldDisproof;
	while(node!= 0 && changed)
	{
		oldProof = node->proof;
		oldDisproof = node->disproof;
		SetProofAndDisproofNumbers(node);
		changed =	(oldProof!=node->proof)||
					(oldDisproof != node->disproof);
		previousNode = node;
		node = node->parent;
		RemoveAStone(previousNode);
	}
	PutAStone(previousNode);
	return previousNode;
}


void ExpandNode(PtrNode node)
{
	GenerateAllChildren(node);
	for ( int i = 0 ; i < node->numOfChildren ;++ i )
	{
		PutAStone(node->children[i]);
		Evaluate(node->children[i]);
		SetProofAndDisproofNumbers(node->children[i]);
		RemoveAStone(node->children[i]);
	}
	node->expanded = true;
}
void pns()
{
	Evaluate(root);
	SetProofAndDisproofNumbers(root);
	PtrNode CurrentNode = root;
	PtrNode mostPNode;
	while(root->proof != 0 && root->disproof != 0 && ResourceAvailable())
	{
		mostPNode = SelectMostProving(CurrentNode);
		ExpandNode(mostPNode);
		CurrentNode = UpdateAncestors(mostPNode);
	}
	if(root->proof == 0)
	{
		root->value = TRUE;
	}
	else if ( root->disproof == 0 )
	{
		root->value = FALSE;
	}
	else
	{
		root->value = UNKNOWN;
	}
}
void startPns()
{
	totalNode = 0;
	root = GetOneNode();

	root->type = OR;
	root->moves=0;
	root->x = -1;
	root->y= -1;
	for (int x = 0; x < width; ++ x )
	{
		for ( int y = 0 ; y < height; ++ y)
		{
			//root->board[x][y]= board[x][y];
			if(board[x][y] !=0)
			{
				++root->moves;
			}
		}
	}
	pns();
}
