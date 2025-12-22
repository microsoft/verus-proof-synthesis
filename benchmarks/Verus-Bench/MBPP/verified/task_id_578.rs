use vstd::prelude::*;

fn main() {
    //Write a function in Rust to interleave 3 lists of the same length into a single flat list.

    assert_eq!(
        interleave(
            &vec![1, 2, 3, 4, 5, 6, 7],
            &vec![10, 20, 30, 40, 50, 60, 70],
            &vec![100, 200, 300, 400, 500, 600, 700]
        ),
        [1, 10, 100, 2, 20, 200, 3, 30, 300, 4, 40, 400, 5, 50, 500, 6, 60, 600, 7, 70, 700]
    );
    assert_eq!(
        interleave(&vec![10, 20], &vec![15, 2], &vec![5, 10]),
        [10, 15, 5, 20, 2, 10]
    );
    assert_eq!(
        interleave(&vec![11, 44], &vec![10, 15], &vec![20, 5]),
        [11, 10, 20, 44, 15, 5]
    );
}

verus! {

fn interleave(s1: &Vec<i32>, s2: &Vec<i32>, s3: &Vec<i32>) -> (res: Vec<i32>)
    requires
        s1@.len() == s2@.len() && s2@.len() == s3@.len(),
        0 <= (s1@.len() * 3) <= i32::MAX,
    ensures
        res@.len() == s1@.len() * 3,
        forall|i: int|
            0 <= i < s1@.len() ==> (res[3 * i] == s1[i] && res[3 * i + 1] == s2[i] && res[3 * i + 2]
                == s3[i]),
{
    let new_seq_len = s1.len() * 3;
    let mut output_seq = Vec::with_capacity(new_seq_len);
    let mut index = 0;

    while index < s1.len()
        invariant
            0 <= index <= s1.len(),
            output_seq@.len() == 3 * index,
            s1@.len() == s2@.len() && s2@.len() == s3@.len(),
            forall|k: int|
                0 <= k < index ==> (output_seq[3 * k] == s1[k] && output_seq[3 * k + 1] == s2[k]
                    && output_seq[3 * k + 2] == s3[k]),
    {
        output_seq.push(s1[index]);
        output_seq.push(s2[index]);
        output_seq.push(s3[index]);
        index += 1;
    }
    output_seq
}

} // verus!
