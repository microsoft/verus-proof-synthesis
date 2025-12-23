
use vstd::prelude::*;
fn main() {}
verus! {
/*
 This lemma is often useful to put right after a loop that has a loop invariant involving Seq::take(i), with i being the loop index.
 Example usage:
    while ( k < s.len() )
      invariant
          ...
          k <= s.len(),
          ...s@.take(k as int)...,
          ...
    {
       ...
       k = k + 1;
    }
	lemma_seq_take_all(s@);
*/
proof fn lemma_seq_take_all<T>(v: Seq<T>)
    ensures
        v == v.take(v.len() as int),
{
    assert(v =~= v.take(v.len() as int));
}


/*
 This lemma is often useful to put near the end of a loop body that has a loop invariant involving Seq::take(i), with i being the loop index.
 Example usage:
    while ( k < s.len() )
      invariant
          ...
          k <= s.len(),
          ...s@.take(k as int)...,
          ...
    {
       ...
       k = k + 1;
       proof{
        lemma_seq_take_ascend(s@, k as int);
       }
    }
*/
proof fn lemma_seq_take_ascend<T>(v: Seq<T>, i: int)
    requires
        0 < i <= v.len(),
    ensures
        v.take(i as int).drop_last() == v.take(i-1),
{
    assert(v.take(i as int).drop_last()=~=v.take(i-1));
}



#[verifier::loop_isolation(false)]

spec fn is_lower_case(c: char) -> bool {
    (c as u32) >= 97 && (c as u32) <= 122
}

spec fn is_upper_case(c: char) -> bool {
    (c as u32) >= 65 && (c as u32) <= 90
}

spec fn count_uppercase_recursively(seq: Seq<char>) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_uppercase_recursively(seq.drop_last()) + if is_upper_case(seq.last()) {
            1 as int
        } else {
            0 as int
        }
    }
}

fn count_uppercase(text: &Vec<char>) -> (count: u64)
    ensures
        0 <= count <= text.len(),
        count_uppercase_recursively(text@) == count,
{
    let mut index = 0;
    let mut count = 0;
    
    // Adding the assertion just before the loop starts
    assert(forall |k: int| 0 <= k < text.len() ==> is_lower_case(text[k]) || is_upper_case(text[k]));
    
    while index < text.len()
        invariant
            0 <= count <= index,
            0 <= index <= text.len(),
            text.len() == text.len(),
            count_uppercase_recursively(text@.take(index as int)) == count as int,
            // Existing invariant for elements in array
            forall |k: int| 0 <= k < text.len() ==> is_lower_case(text[k]) || is_upper_case(text[k]),
    {
        if ((text[index] as u32) >= 65 && (text[index] as u32) <= 90) {
            count += 1;
        }
        index += 1;
        proof {
            if index > 0 {
                lemma_seq_take_ascend(text@, index as int);
            }
            if index == text.len() {
                lemma_seq_take_all(text@);
            }
            assert(count_uppercase_recursively(text@.take(index as int)) == count as int);
        }
    }
    count
}

} // verus!


//             assert(count_uppercase_recursively(text@.take(index as int)) == count as int);
//   assertion failed: count_uppercase_recursively(text@.take(index as int)) == count as int

// Compilation Error: False, Verified: 4, Errors: 1, Verus Errors: 2
// Safe: True