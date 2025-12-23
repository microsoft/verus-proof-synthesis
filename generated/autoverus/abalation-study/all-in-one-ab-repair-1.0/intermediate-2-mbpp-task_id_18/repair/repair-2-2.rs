
use vstd::prelude::*;
fn main() {}

verus! {

    spec fn contains_spec(str: Seq<char>, key: char) -> bool {
        exists|i: int| 0 <= i < str.len() && str[i] == key
    }

    spec fn remove_chars_spec(str1: Seq<char>, str2: Seq<char>) -> Seq<char> {
        str1.filter(|c| !contains_spec(str2, *c))
    }

    #[verifier::proof]
    #[verifier::returns(spec)]
    fn contains(str: &Vec<char>, key: char) -> bool
        ensures
            result <==> contains_spec(str@, key)
    {
        let mut i = 0;
        while i < str.len()
            invariant
                forall|j: int| 0 <= j < i ==> str[j] != key,
                i <= str.len(),
                forall |k:int| 0<=k<str.len() ==> str[k] == str@(k),
        {
            if str[i] == key {
                return true;
            }
            i += 1;
        }
        false
    }

    #[verifier::proof]
    #[verifier::returns(spec)]
    fn remove_chars(str1: &Vec<char>, str2: &Vec<char>) -> Vec<char>
        ensures
            result@ == remove_chars_spec(str1@, str2@)
    {
        let mut output_str = Vec::new();
        let mut index = 0;
        while index < str1.len()
            invariant
                forall|i: int| 0 <= i < index ==> str2@.contains(str1[i]) || output_str@.contains(str1[i]),
                forall|i: int| 0 <= i < output_str.len() ==> str1@.contains(output_str[i]) && !str2@.contains(output_str[i]),
                index <= str1.len(),
                output_str.len() <= index,
                forall |k:int| 0<=k<str1.len() ==> str1[k] == str1@(k),
                forall |k:int| 0<=k<str2.len() ==> str2[k] == str2@(k),
        {
            if !contains(str2, str1[index]) {
                output_str.push(str1[index]);
            }
            index += 1;
        }
        output_str
    }

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp3ipzktgt`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False