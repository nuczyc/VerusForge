
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn bit_wise_xor(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    requires
        arr1.len() == arr2.len(),
    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> result[i] == #[trigger] arr1[i] ^ #[trigger] arr2[i],
{
    let mut output_arr = Vec::with_capacity(arr1.len());
    let mut index = 0;
    while index < arr1.len()
    invariant
        arr1.len() == arr2.len(),
        arr1.len() == output_arr.len() + (arr1.len() - index),
        forall |j: int| 0 <= j < output_arr.len() ==> output_arr[j] == arr1[j] ^ arr2[j],
        // arr1 and arr2 are never modified in the loop
        forall |k:int| 0 <= k < arr1.len() ==> arr1[k] == arr1[k],
        forall |k:int| 0 <= k < arr2.len() ==> arr2[k] == arr2[k],
    decreases
        arr1.len() - index,
    {
        output_arr.push((arr1[index] ^ arr2[index]));
        index += 1;
    }
    proof {
        let final_len = arr1.len();
        assert(arr1.len() == output_arr.len() + (arr1.len() - index));
        assert(index == arr1.len()) by {
            assert(arr1.len() == output_arr.len() + (arr1.len() - index));
            assert(output_arr.len() == arr1.len() - (arr1.len() - index));
            assert(output_arr.len() == index);
        }
        assert(index == final_len);
        assert(output_arr.len() == final_len);
    }
    output_arr
}

} // verus!

// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True