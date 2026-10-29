
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

proof fn element_wise_subtract_invariant(len: nat)
    ensures
        len == len,
{}

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
            // Maintain the precondition that arr1 and arr2 remain immutable and valid
            forall|k: int| 0 <= k < arr1.len() ==> (arr1[k] == arr1[k]),
            forall|k: int| 0 <= k < arr2.len() ==> (arr2[k] == arr2[k]),
            // Maintain invariant relating to output_arr values.
            forall|i: int| 0 <= i < output_arr.len() ==> output_arr[i] == (arr1[i] - arr2[i]),
        decreases arr1.len() - index
    {
        assert(i32::MIN <= arr1[( index ) as int] - arr2[( index ) as int] <= i32::MAX);
        output_arr.push((arr1[index] - arr2[index]));
        index += 1;
    }
    proof {
        assert(output_arr.len() == arr1.len());
        element_wise_subtract_invariant((arr1.len()) as nat);
    }
    output_arr
}

} // verus!




// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2
// Safe: True