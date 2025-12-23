
use vstd::prelude::*;
fn main() {}

/// Verus! macro for formal verification
verus! {

    // Spec function to check if a character is a digit
    spec fn is_digit(c: char) -> bool {
        (c as u8) >= 48 && (c as u8) <= 57
    }

    // Recursive specification function to count digits in a sequence
    spec fn count_digits_recursively(seq: Seq<char>) -> int
        decreases seq.len(), // Decreases clause for termination
    {
        if seq.len() == 0 {
            0
        } else {
            count_digits_recursively(seq.drop_last()) + if is_digit(seq.last()) {
                1 as int
            } else {
                0 as int
            }
        }
    }

    // Function to count digits in a vector of characters
    fn count_digits(text: &Vec<char>) -> (count: usize)
        ensures
            0 <= count <= text.len(), // Ensuring count is within valid bounds
            count_digits_recursively(text@) == count, // Ensuring function result matches spec
    {
        let mut count = 0;
        let mut index = 0;
        
        // Loop to iterate over the text and count digits
        while index < text.len()
            invariant
                0 <= count, // Count should be non-negative
                count <= index, // Count should not exceed the current index
                index <= text.len(), // Index should be within the text length
        {
            // Checking if the current character in text is a digit
            if ((text[index] as u8) >= 48 && (text[index] as u8) <= 57) {
                count += 1; // Increment count if the character is a digit
            }
            index += 1; // Move to the next character
        }
        count // Return the total count of digits
    }
}


// Score: Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1