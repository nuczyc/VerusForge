
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

proof fn index_equals_len(index: usize, len: usize)
    requires index == len
    ensures index == len
{}

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
            output_arr.len() == index,
            forall|j: int|
                0 <= j < index ==> output_arr[j] == #[trigger] arr1[j] ^ #[trigger] arr2[j],
        decreases arr1.len() - index,
    {
        output_arr.push((arr1[index] ^ arr2[index]));
        index += 1;
    }
    assert(output_arr.len() == arr1.len()) by {
        assert(output_arr.len() == index);
        index_equals_len(index, arr1.len());
    }
    output_arr
}

}

// Score: Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1
// Safe: True