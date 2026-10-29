
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]
fn element_wise_division(arr1: &Vec<u32>, arr2: &Vec<u32>) -> (result: Vec<u32>)
    requires
        arr1.len() == arr2.len(),
        forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
        forall|m: int| 0 <= m < arr1.len() ==> (u32::MIN <= #[trigger] arr1[m] / #[trigger] arr2[m]
                <= u32::MAX),
    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] / arr2[i]),
{
    let mut output_arr = Vec::with_capacity(arr1.len());
    let mut index = 0;

    while index < arr1.len()
        invariant
            arr1.len() == arr2.len(),
            output_arr.len() == index,
            forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
            forall|m: int| 0 <= m < arr1.len() ==> (u32::MIN <= #[trigger] arr1[m] / #[trigger] arr2[m] <= u32::MAX),
            forall|k: int| 0 <= k < arr1.len() ==> (u32::MIN <= #[trigger] arr1[k] / #[trigger] arr2[k] <= u32::MAX),
            forall|j: int| 0 <= j < index ==> output_arr[j] == (arr1[j] / arr2[j]),
        decreases arr1.len() - index,
    {
        output_arr.push((arr1[index] / arr2[index]));
        index += 1;
    }
    proof {
        assert(forall|i: int| 0 <= i < output_arr.len() ==> #[trigger] output_arr[i] == (arr1[i] / arr2[i]));
        assert(output_arr.len() == arr1.len());
    }
    output_arr
}

} // verus!

// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True