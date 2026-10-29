
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn element_wise_subtract(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    requires
        arr1.len() == arr2.len(),
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] - arr2[i]) <= i32::MAX),
    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] - arr2[i]),
{
    let mut output_arr = Vec::with_capacity(arr1.len());
    let mut index = 0;
    while index < arr1.len() 
    invariant
        arr1.len() == arr2.len(),
        output_arr.len() <= arr1.len(),
        forall|k: int| 0 <= k < output_arr.len() ==> #[trigger] output_arr[k] == (arr1[k] - arr2[k]), 
    decreases arr1.len() - index, 
    {
        output_arr.push((arr1[index] - arr2[index]));
        index += 1;
        proof {
            assert(forall|k: int| 0 <= k < output_arr.len() ==> #[trigger] output_arr[k] == (arr1[k] - arr2[k])) by {
                assert(forall|k: int| 0 <= k < output_arr.len() - 1 ==> #[trigger] output_arr[k] == (arr1[k] - arr2[k]));
                assert(output_arr.len() > 0);
                let last_index = output_arr.len() - 1;
                assert(#[trigger] output_arr[last_index] == (arr1[last_index] - arr2[last_index]));
            };
        } 
    }
    output_arr
}

}

// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 2
// Safe: True