
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    fn get_first_elements(arr: &Vec<Vec<i32>>) -> (result: Vec<i32>)
        requires
            forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() > 0,
        ensures
            arr.len() == result.len(),
            forall|i: int| 0 <= i < arr.len() ==> #[trigger] result[i] == #[trigger] arr[i][0],
    {
        let mut first_elem_arr: Vec<i32> = Vec::new();
        let mut index = 0;
        while index < arr.len()
            invariant
                first_elem_arr.len() == index,
                forall|i: int| 0 <= i < index ==> #[trigger] first_elem_arr[i] == #[trigger] arr[i][0],
                index <= arr.len(),
        {
            let seq = &arr[index];
            first_elem_arr.push(seq[0]);
            index += 1;
        }
        first_elem_arr
    }
    
    #[verifier::prove]
    fn test() {
        let arr = vec![
            vec![1, 2, 3],
            vec![4, 5, 6],
            vec![7, 8, 9],
        ];
        
        let result = get_first_elements(&arr);
        
        assert(arr.len() == result.len());
        assert(forall(|i: usize| 0 <= i < arr.len() ==> result[i] == arr[i][0]));
    }
}



// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpknw2gctn`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False