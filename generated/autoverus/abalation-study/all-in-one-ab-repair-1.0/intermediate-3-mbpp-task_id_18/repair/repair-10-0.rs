
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
    {
        if (str[i] == key) {
            proof {
                assert(exists|k: int| 0 <= k < str.len() && str[k] == key);
            } // Added by AI
            return true;
        }
        i += 1;
    }
    proof {
        assert(!exists|k: int| 0 <= k < str.len() && str[k] == key);
    } // Added by AI
    false
}

fn remove_chars(str1: &Vec<char>, str2: &Vec<char>) -> (result: Vec<char>)
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (str1@.contains(#[trigger] result[i]) && !str2@.contains(
                #[trigger] result[i],
            )),
        forall|i: int|
            0 <= i < str1.len() ==> (str2@.contains(#[trigger] str1[i]) || result@.contains(
                #[trigger] str1[i],
            )),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;
    while index < str1.len()
        invariant
            forall|i: int|
                0 <= i < index ==> (str2@.contains(#[trigger] str1[i]) || output_str@.contains(
                    #[trigger] str1[i],
                )),
            forall|i: int|
                0 <= i < output_str.len() ==> (str1@.contains(#[trigger] output_str[i])
                    && !str2@.contains(#[trigger] output_str[i])),
            index <= str1.len(),
            output_str.len() <= index,
    {
        if (!contains(str2, str1[index])) {
            output_str.push(str1[index]);
            proof {
                let new_len = output_str.len();
                assert(new_len > 0);
                assert(str1@.contains(output_str[new_len - 1]));
                assert(!str2@.contains(output_str[new_len - 1]));
            } // Added by AI
        }
        index += 1;
    }
    proof {
        assert(forall|i: int| 0 <= i < result.len() ==> str1@.contains(result[i]) && !str2@.contains(result[i]));
        assert(forall|i: int| 0 <= i < str1.len() ==> str2@.contains(str1[i]) || result@.contains(str1[i]));
    } // Added by AI
    output_str
}

}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmppiz9shuq`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: True