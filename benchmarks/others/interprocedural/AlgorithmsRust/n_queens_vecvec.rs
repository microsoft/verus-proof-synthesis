/*
This is an attempt of turning the following N Queens Rust implementation into Verus
https://github.com/TheAlgorithms/Rust/blob/master/src/backtracking/n_queens.rs

A couple of notes:
1. A couple of features related to Vec<Vec<...>> are currently not supported by Verus 
 let  board = vec![vec!['.'; n]; n];
 board[row][col] = c;
As a result, I used a nested loop to implement board = vec![vec!['.'; n]; n]
And, I had to put board[row][col] = c into a Verus external function

2. The reading of board[row][col] *is* supported by Verus.
In fact, Verus would check buffer overflow at both levels/dimensions.
As a result, it takes a lot of specification to prove the free of buffer overflows, 
much more spec than proving free of overflow in a one-dimensional Vec.

3. There actually ARE arithmetic overflow in the original implementation.
 let mut j : i32 = col as i32 - (row as i32 - i as i32);
 and
 let j = col + row - i;
 in the is_safe function

 I added the board.len() < 1000 constraint so that Verus won't complain about arithmetic overflow.
*/

use vstd::prelude::*;
 
verus!{

    pub fn main () {
        let solutions = n_queens_solver(4);
    }

    

    #[verifier::external_body]
	fn myVecClone(v: &Vec<Vec<char>>) -> Vec<Vec<char>> {
		v.clone()
	}

    #[verifier::external_body]
    pub fn setBoard(board: &mut Vec<Vec<char>>, row: usize, col: usize, c: char) 
    requires
        row < old(board).len(),
        col < old(board).len(),
    ensures
        board.len() == old(board).len(),
        forall |i : int| 0<= i < board.len() ==> #[trigger] board@.index(i as int).len() == old(board)@.index(i as int).len(),
    {
         board[row][col] = c;
    }

    pub fn readBoard(board: &Vec<Vec<char>>, row: usize, col: usize) -> char 
    requires
        row < board.len(),
        col < board@.index(row as int).len(),
    {
        board[row][col]
    }

    pub fn init_board(board: &mut Vec<Vec<char>>, n: usize)
    requires
        old(board).len() == 0,
    ensures
        board.len() == n,
        forall |i : int| 0<= i < n ==> #[trigger] board@.index(i as int).len() == n,
    {
        //let  board = vec![vec!['.'; n]; n];
         
        let mut i = 0;
        while i < n
        invariant
            board.len() == i,
            forall |k : int| 0<= k < i ==> #[trigger] board@.index(k as int).len() == n,
            i <= n,
        {
            let mut j = 0;
            let mut row: Vec<char> = vec![];
            while j < n
            invariant
                row.len() == j,
                j <= n,
            {
                row.push('.');
                j = j + 1;
            }
            board.push(row);
            i = i + 1;
        }
        
    }

    pub fn n_queens_solver(n: usize) -> Vec<Vec<Vec<char>>> 
    requires
        n < 1000,//added by Shan to eliminate potential arithmetic overflow 
    {
        let mut board: Vec<Vec<char>> = vec![];
        init_board(&mut board, n);
        let mut solutions: Vec<Vec<Vec<char>>> = vec![];
        solve(&mut board, 0, &mut solutions);
        solutions
    }
    
    fn is_safe(board: &Vec<Vec<char>>, row: usize, col: usize) -> bool 
    requires
        row < board.len(),
        col < board.len(),
        forall |i : int| 0<= i < board.len() ==> #[trigger] board@.index(i as int).len() == board.len(),
        board.len() < 1000,
    {
        // Check if there is a queen in the same column
        let mut i = 0;
        while i < board.len()
        invariant
            row < board.len(),
            col < board@.index(row as int).len(), 
        {
            if readBoard(board, row, col) == 'Q' {
                return false;
            }
            i = i + 1;
        }
    

        
        // Check if there is a queen in the left upper diagonal
        let mut i = 0;
        while i < row 
        invariant
            row < board.len(),
            col < board.len(),
            forall |i : int| 0<= i < board.len() ==> #[trigger] board@.index(i as int).len() == board.len(),
            board.len() < 1000,
        {
            
            let mut j : i32 = col as i32 - (row as i32 - i as i32);
            if j >=0 && readBoard(board, i, j as usize) == 'Q' {
                return false;
            }
            i = i + 1;
        }

   
        // Check if there is a queen in the right upper diagonal
        let mut i = 0;
        while i < row 
        invariant
            col < board.len(),
            row < board.len(),
            forall |i : int| 0<= i < board.len() ==> #[trigger] board@.index(i as int).len() == board.len(),
            board.len() < 1000,
        {

            let j = col + row - i;
            
            if j < board.len() && readBoard(board, i, j) == 'Q' {
                return false;
            }
            i = i+1;
        }
            
        true
    }
    
    fn solve(board: &mut Vec<Vec<char>>, row: usize, solutions: &mut Vec<Vec<Vec<char>>>) 
    requires
        row <= old(board).len(),
        forall |i : int| 0<= i < old(board).len() ==> #[trigger] old(board)@.index(i as int).len() == old(board).len(),
        old(board).len() < 1000,
    ensures
        board.len() == old(board).len(),
        forall |i : int| 0<= i < board.len() ==> #[trigger] board@.index(i as int).len() == old(board)@.index(i as int).len(),
    {
     
        if row == board.len() {
            solutions.push(myVecClone(board));
            return;
        }
     
        let mut col = 0;

        while col < board.len() 
        invariant
            row < board.len(),
            board.len() < 1000,
            board.len() == old(board).len(),
            forall |i : int| 0<= i < board.len() ==> #[trigger] board@.index(i as int).len() == board.len(),
        {
            if is_safe(board, row, col) {
                setBoard(board, row, col, 'Q');
                solve(board, row + 1, solutions);
                setBoard(board, row, col, '.');
            }
            col = col + 1;
        }
     
    }

}
