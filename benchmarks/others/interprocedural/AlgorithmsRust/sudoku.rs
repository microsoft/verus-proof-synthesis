/*

This example is from Algorithm/Rust project.
https://github.com/TheAlgorithms/Rust/blob/master/src/backtracking/sudoku.rs

The original test cases test_sudoku_correct and test_sudoku_incorrect cannot be easily convereted to verification properties.
Instead, the added proof helps to verify the program free of arithemtic overflow and buffer overflow.

The main function is essentially the test_sudoku_correct function without the two run-time asserts.

*/

use vstd::prelude::*;

 
verus!{

	fn main() {
		
		let board: [u8; 81] = [
				3, 0, 6, 5, 0, 8, 4, 0, 0,
				5, 2, 0, 0, 0, 0, 0, 0, 0,
				0, 8, 7, 0, 0, 0, 0, 3, 1,
				0, 0, 3, 0, 1, 0, 0, 8, 0,
				9, 0, 0, 8, 6, 3, 0, 0, 5,
				0, 5, 0, 0, 9, 0, 6, 0, 0,
				1, 3, 0, 0, 0, 0, 2, 5, 0,
				0, 0, 0, 0, 0, 0, 0, 7, 4,
				0, 0, 5, 2, 0, 6, 3, 0, 0,
			];
	
		let board_result = [
				3, 1, 6, 5, 7, 8, 4, 9, 2,
				5, 2, 9, 1, 3, 4, 7, 6, 8,
				4, 8, 7, 6, 2, 9, 5, 3, 1,
				2, 6, 3, 4, 1, 5, 9, 8, 7,
				9, 7, 4, 8, 6, 3, 1, 2, 5,
				8, 5, 1, 7, 9, 2, 6, 4, 3,
				1, 3, 8, 9, 4, 7, 2, 5, 6,
				6, 9, 2, 3, 5, 1, 8, 7, 4,
				7, 4, 5, 2, 8, 6, 3, 1, 9,
			];
	
		let mut sudoku: Sudoku = Sudoku::new(board);
		let is_solved: bool = sudoku.solve();

	}

	 
	pub struct Sudoku {
		board: [u8; 81],
	}
	
	impl Sudoku {
		pub fn new(board: [u8; 81]) -> Sudoku {
			Sudoku { board }
		}

		fn setcell(&mut self, x: usize, y: usize, val: u8) 
		requires
			0 <= x < 9,
			0 <= y < 9,
		{
			self.board.set(x*9 + y, val);
		}

		fn readcell(&self, x: usize, y: usize) -> u8 
		requires
			0 <= x < 9,
			0 <= y < 9,
		
		{
			self.board[x*9 + y]
		}
	
		fn find_empty_cell(&self) -> (ret: Option<(usize, usize)>) 
		ensures
		 match ret {
			Some((x, y)) => 0 <= x < 9 && 0 <= y < 9,
			None => true,
		 }
		{
			// Find a empty cell in the board (returns None if all cells are filled)
			let mut i = 0;
			while i < 9 
			invariant
				0 <= i,
			{
				let mut j = 0;
				while j < 9 
				invariant
					0 <= i <9,
					0 <= j,
				{
					if self.readcell(i, j) == 0 {
						return Some((i, j));
					}
					j += 1;
				}
				i += 1;
			}
	
			None
		}
	
		fn check(&self, index_tuple: (usize, usize), value: u8) -> bool 
		requires
			0 <= index_tuple.0 < 9,
			0 <= index_tuple.1 < 9,
		{
			let (y, x) = index_tuple;

			let mut i = 0;
			let mut j = 0;
	
			// checks if the value to be added in the board is an acceptable value for the cell
	
			// checking through the row
			while i < 9 
			invariant 
				0 <= x < 9,
			{
				if self.readcell(i, x) == value {
					return false;
				}
				i += 1;
			}
			// checking through the column
			i = 0;
			while i < 9 
			invariant
				0 <= y < 9,
			{
				if self.readcell(y,i) == value {
					return false;
				}
				i += 1;
			}
	
			// checking through the 3x3 block of the cell
			let sec_row = y / 3;
			let sec_col = x / 3;
	
			i = sec_row * 3;
			while i < (sec_row * 3 + 3) 
			invariant
				0 <= sec_col < 3,
				0 <= sec_row < 3,
			{
				j = sec_col * 3;
				while j < (sec_col * 3 + 3) 
				invariant
					0 <= sec_col < 3,
					0 <= sec_row < 3,
					0 <= i < 9,
				{
					if self.readcell(i,j) == value {
						return false;
					}
					j = j + 1;
				}
				i = i + 1;
			}
	
			true
		}
	
		pub fn solve(&mut self) -> bool {
			let empty_cell = self.find_empty_cell();
	
			if let Some((y, x)) = empty_cell {
				let mut val = 1;
				while val < 10 
				invariant
					0 <= val <= 10,
					0 <= x < 9,
					0 <= y < 9,
				
				{
					if self.check((y, x), val) {
						self.setcell(y, x, val);
						if self.solve() {
							return true;
						}
						// backtracking if the board cannot be solved using current configuration
						self.setcell(y, x, 0);
						//self.board[y][x] = 0
					}
					val += 1;
				}
			} else {
				// if the board is complete
				return true;
			}
	
			// returning false the board cannot be solved using current configuration
			false
		}
	}
	/*
	//#[cfg(test)]
	mod tests {
		use super::*;
	
		//#[test]
		pub fn test_sudoku_correct() {
			let board: [[u8; 9]; 9] = [
				[3, 0, 6, 5, 0, 8, 4, 0, 0],
				[5, 2, 0, 0, 0, 0, 0, 0, 0],
				[0, 8, 7, 0, 0, 0, 0, 3, 1],
				[0, 0, 3, 0, 1, 0, 0, 8, 0],
				[9, 0, 0, 8, 6, 3, 0, 0, 5],
				[0, 5, 0, 0, 9, 0, 6, 0, 0],
				[1, 3, 0, 0, 0, 0, 2, 5, 0],
				[0, 0, 0, 0, 0, 0, 0, 7, 4],
				[0, 0, 5, 2, 0, 6, 3, 0, 0],
			];
	
			let board_result = [
				[3, 1, 6, 5, 7, 8, 4, 9, 2],
				[5, 2, 9, 1, 3, 4, 7, 6, 8],
				[4, 8, 7, 6, 2, 9, 5, 3, 1],
				[2, 6, 3, 4, 1, 5, 9, 8, 7],
				[9, 7, 4, 8, 6, 3, 1, 2, 5],
				[8, 5, 1, 7, 9, 2, 6, 4, 3],
				[1, 3, 8, 9, 4, 7, 2, 5, 6],
				[6, 9, 2, 3, 5, 1, 8, 7, 4],
				[7, 4, 5, 2, 8, 6, 3, 1, 9],
			];
	
			let mut sudoku = Sudoku::new(board);
			let is_solved = sudoku.solve();
	
			assert!(is_solved);
			assert_eq!(sudoku.board, board_result);
		}
	
		//#[test]
		pub fn test_sudoku_incorrect() {
			let board: [[u8; 9]; 9] = [
				[6, 0, 3, 5, 0, 8, 4, 0, 0],
				[5, 2, 0, 0, 0, 0, 0, 0, 0],
				[0, 8, 7, 0, 0, 0, 0, 3, 1],
				[0, 0, 3, 0, 1, 0, 0, 8, 0],
				[9, 0, 0, 8, 6, 3, 0, 0, 5],
				[0, 5, 0, 0, 9, 0, 6, 0, 0],
				[1, 3, 0, 0, 0, 0, 2, 5, 0],
				[0, 0, 0, 0, 0, 0, 0, 7, 4],
				[0, 0, 5, 2, 0, 6, 3, 0, 0],
			];
	
			let mut sudoku = Sudoku::new(board);
			let is_solved = sudoku.solve();
	
			assert!(!is_solved);
		}
	}
 
	*/
}
     
