
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

proof fn assert_index_equals_len(index: usize, arr1: &Vec<u32>)
    requires
        index <= arr1.len(),
    ensures
        index == arr1.len(),
{
    assert(index == arr1.len());
}

fn element_wise_division(arr1: &Vec<u32>, arr2: &Vec<u32>) -> (result: Vec<u32>)
    requires
        arr1.len() == arr2.len(),
        forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
        forall|m: int|
            0 <= m < arr1.len() ==> (u32::MIN <= #[trigger] arr1[m] / #[trigger] arr2[m]
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
            forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
            forall|m: int|
                0 <= m < arr1.len() ==> (u32::MIN <= #[trigger] arr1[m] / #[trigger] arr2[m]
                    <= u32::MAX),
            forall|i: int| 0 <= i < arr1.len() ==> arr1[i] == arr1[i],
            output_arr.len() == index,
            arr1.len() == arr2.len(),
            forall|i: int| 0 <= i < index ==> output_arr[i] == (arr1[i] / arr2[i]),
        decreases
            arr1.len() - index,
    {
        output_arr.push((arr1[index] / arr2[index]));
        index += 1;
    }
    
    proof {
        assert(output_arr.len() == arr1.len()) by {
            assert(output_arr.len() == index);
            assert_index_equals_len(index, arr1);
        }
    }
    
    output_arr
}

}

// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2
// Safe: True