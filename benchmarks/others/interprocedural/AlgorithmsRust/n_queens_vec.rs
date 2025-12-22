/*
This is another attempt of turning the following N Queens Rust implementation into Verus
https://github.com/TheAlgorithms/Rust/blob/master/src/backtracking/n_queens.rs

There are several issues here:
1. Since Verus has various constraints in its support to vec<vec>, in this implemnetation, I flatterned Vec<vec> into Vec<>
However, this led to a LOT of trouble in non-linear arithmetic related verification.

2. Because of my use of vec<>, there is now a side-effect of potential arithmetic overflow of n*n
 I added the board.len() < 1000 constraint so that Verus won't complain about arithmetic overflow.
*/

use vstd::prelude::*;
//use vstd::string::*;
 
verus!{

    pub fn main () {
        let solutions = n_queens_solver(4);
    }

    pub fn readBoard(board: &Vec<char>, row: usize, col: usize, n: usize) -> char 
    requires
        board.len() == n * n,
        row < n,
        col < n,
        n < 1000,
    {
        assert(row* n + col < n * n) by (nonlinear_arith)
        requires
            row <= n - 1, //change from row < n to row <= n-1 can cut Verus time by a LOT
            col < n, 
        {

        }
        assert(row * n + col < usize::MAX);
        assert(row * n + col >= 0) by (nonlinear_arith);
  
        assert(row * n < usize::MAX) by (nonlinear_arith)
        requires
            row < n,
            n < 1000,
        {};
        assert(row * n >=0) by (nonlinear_arith);

        board[row* n + col]
    }

    pub fn setBoard(board: &mut Vec<char>, row: usize, col: usize, n: usize, c: char) 
    requires
        old(board).len() == n * n,
        row < n,
        col < n,
        n < 1000,
    ensures
        board.len() == n * n,
    {
        assert( row*n + col < n * n) by (nonlinear_arith)
        requires
            row < n,
            col < n,
            {}
        assert(row*n + col < usize::MAX);
        assert(row*n + col >=0) by (nonlinear_arith);
        assert(row*n < usize::MAX);
        assert(row*n >=0) by (nonlinear_arith);
        board.set(row*n + col, c);
    }

    #[verifier::external_body]
	fn myVecClone(v: &Vec<char>) -> Vec<char> {
		v.clone()
	}

    pub fn init_board(board: &mut Vec<char>, n: usize)
    requires
        n < 1000,
        old(board).len() == 0,
    ensures
        board.len() == n*n,
    {
        let mut i: usize = 0;

        assert(0<= n * n < 1000000) by (nonlinear_arith)
        requires
            n < 1000,
            {}
        
        let bound = n * n;
        while i < bound
        invariant
            board.len() == i,
            i <= bound,
        {
            board.push('.');
            i = i +1;
        }
    }

    pub fn n_queens_solver(n: usize) -> Vec<Vec<char>> 
    requires
        n < 1000,
    {
        let mut board: Vec<char> = vec![];
        init_board(&mut board, n);
        let mut solutions: Vec<Vec<char>> = vec![];
        solve(&mut board, 0, &mut solutions, n);
        solutions
    }
    
    fn is_safe(board: &Vec<char>, row: usize, col: usize, n: usize) -> bool 
    requires
        board.len() == n * n,
        row < n,
        col < n,
        n < 1000, 
    {
        // Check if there is a queen in the same column
        let mut i = 0;
        while i < n 
        invariant
            row < n,
            n < 1000,
            col < n,
            board.len() == n * n,
        {
            if readBoard(board, row, col, n) == 'Q' {
                return false;
            }
            i = i + 1;
        }
    
        // Check if there is a queen in the left upper diagonal
        let mut i = 0;
        while i < row 
        invariant
            row < n,
            col < n,
            n < 1000,
            board.len() == n*n,
        {
            let mut j : i32 = col as i32 - (row as i32 - i as i32);
            if j >=0 && readBoard(board, i, j as usize, n) == 'Q' {
                return false;
            }
            i = i + 1;
        }


        /* for i in (0..row).rev() {
            let j = col as isize - (row as isize - i as isize);
            if j >= 0 && board[i][j as usize] == 'Q' {
                return false;
            }
        }
        */
    
        // Check if there is a queen in the right upper diagonal
        let i = 0;
        while i < row 
        invariant
            col < n,
            row < n,
            n < 1000,
            board.len() == n*n,
        {
            let j = col + row - i;
            if j < n && readBoard(board, i, j, n) == 'Q' {
                return false;
            }
            i = i + 1;
        }
        
        /* 
        for i in (0..row).rev() {
            let j = col + row - i;
            if j < board.len() && board[i][j] == 'Q' {
                return false;
            }
        }
        */
    
        true
    }
    
    fn solve(board: &mut Vec<char>, row: usize, solutions: &mut Vec<Vec<char>>, n: usize) 
    requires
        n < 1000,
        row <= n,
        old(board).len() == n * n,
    ensures
        board.len() == n*n,
    {
    
        if row == n {
            solutions.push(myVecClone(board));
            return;
        }
    
        let mut col = 0;

        while col < n 
        invariant
            row < n,
            board.len() == n * n,
            n < 1000,
        {
            if is_safe(board, row, col, n) {
                setBoard(board, row, col, n, 'Q');
                assert(board.len() == n*n);
                solve(board, row + 1, solutions, n);
                setBoard(board, row, col, n, '.');
            }
            col = col + 1;
        }
    }

}
 
