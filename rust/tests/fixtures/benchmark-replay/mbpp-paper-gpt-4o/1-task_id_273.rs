
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
            output_arr.len() == index, 
            forall|i: int| 0 <= i < index ==> #[trigger] output_arr[i] == #[trigger] (arr1[i] - arr2[i]),
        decreases (arr1.len() - index),
    {
        output_arr.push((arr1[index] - arr2[index]));
        index += 1;
    }
    // Proof block to ensure output_arr.len() matches arr1.len() after the loop
    proof {
        assert(index == arr1.len());
        assert(output_arr.len() == index);
        assert(output_arr.len() == arr1.len()); // Confirmed by proof of invariants
    }
    output_arr
}

} // verus!

// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True