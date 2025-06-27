
use vstd::prelude::*;
fn main() {}

verus! {

fn contains(str: &Vec<char>, key: char) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut i = 0;
    while i < str.len()
        invariant
            forall|j: int| 0 <= j < i ==> str[j] != key,
            i <= str.len(),
            str.len() == str.len(), // Loop invariant for array length
    {
        if str[i] == key {
            return true;
        }
        i += 1;
    }
    false
}

fn remove_chars(str1: &Vec<char>, str2: &Vec<char>) -> (result: Vec<char>)
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (str1@.contains(#[trigger] result[i]) && !str2@.contains(#[trigger] result[i])),
        forall|i: int|
            0 <= i < str1.len() ==> (str2@.contains(#[trigger] str1[i]) || result@.contains(#[trigger] str1[i])),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;
    proof {
        let ghost_rs: Seq<char> = Seq::new(str1.len(), |_| ' '); // Creating a ghost sequence for proving reordering
        let mut output_len: int = 0; // Ghost for length of output_str
        assert(ghost_rs.len() == str1.len()); // Ensuring length match
    }
    while index < str1.len()
        invariant
            forall|i: int|
                0 <= i < index ==> (str2@.contains(#[trigger] str1[i]) || output_str@.contains(#[trigger] str1[i])),
            forall|i: int|
                0 <= i < output_str.len() ==> (str1@.contains(#[trigger] output_str[i]) && !str2@.contains(#[trigger] output_str[i])),
            index <= str1.len(),
            output_str.len() <= index,
            str1.len() == str1.len(), // Loop invariant for array length
            str2.len() == str2.len(), // Loop invariant for array length
            exists|r: Seq<int>| is_reorder_of(r, output_str@ + str1.skip(index), str1@), // Addition of reordering invariant
    {
        if !contains(str2, str1[index]) {
            output_str.push(str1[index]);
            proof { output_len += 1; }
        }
        index += 1;
        proof {
            let r = Seq::new(output_len, |j: int| (if j < output_len && j >= 0 { output_str[j] } else { ' ' }) as int);
            assert(exists|r: Seq<int>| is_reorder_of(r, output_str@, str1@));
        }
    }
    proof {
        let r_final = Seq::new(str1.len(), |i: int| (if i < output_str.len() && i >= 0 { output_str[i] } else { ' ' }) as int);
        assert(exists|r: Seq<int>| is_reorder_of(r, output_str@, str1@));
    }
    output_str
}

}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp88r6di8q`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 6
// Safe: False