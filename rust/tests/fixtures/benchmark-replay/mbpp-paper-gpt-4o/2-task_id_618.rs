
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn element_wise_divide(arr1: &Vec<u32>, arr2: &Vec<u32>) -> (result: Vec<u32>)
    requires
        arr1.len() == arr2.len(),
        forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] / arr2[i]) <= i32::MAX),
    ensures
        result@.len() == arr1@.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] / arr2[i]),
{
    let mut output_arr = Vec::with_capacity(arr1.len());
    let mut index = 0;
    while index < arr1.len() invariant
        arr1.len() == arr2.len(),
        arr1.len() == output_arr.len() + (arr1.len() - index),
        forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
        forall|k: int| (0 <= k < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[k] / arr2[k]) <= i32::MAX),
        forall|j: int| 0 <= j < index ==> output_arr[j] == (arr1[j] / arr2[j]),
        decreases (arr1.len() - index),
    {
        output_arr.push((arr1[index] / arr2[index]));
        index += 1;
    }
    proof {
        assert(arr1.len() == output_arr.len()); // Added by AI
        helper_length_proof(arr1.len(), output_arr@);
    } 
    output_arr
}

proof fn helper_length_proof(arr_len: usize, output_seq: Seq<u32>)
    requires
        arr_len == output_seq.len(),
    ensures
        output_seq.len() == arr_len,
{
    assert(output_seq.len() == arr_len);
}

}

// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1
// Safe: True