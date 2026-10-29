use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

proof fn lemma_preserve_length_of_output(arr1: Seq<i32>, output_arr: Seq<i32>, index: int)
    requires
        arr1.len() == index,
        output_arr.len() == index,
    ensures
        output_arr.len() == arr1.len(),
{
    assert(output_arr.len() == arr1.len()) by {
        assert(output_arr.len() == index);
        assert(arr1.len() == index);
    }
}

fn bit_wise_xor(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    requires
        arr1.len() == arr2.len(),
    ensures
        result.len() == arr1.len(),
        forall |i: int|
            0 <= i < result.len() ==> result[i] == #[trigger] arr1[i] ^ #[trigger] arr2[i],
{
    let mut output_arr = Vec::with_capacity(arr1.len());
    let mut index = 0;
    while index < arr1.len()
    invariant
        arr1.len() == arr2.len(),
        output_arr.len() == index,
        forall |k: int| 0 <= k < index ==> output_arr[k] == arr1[k] ^ arr2[k],
    decreases
        arr1.len() - index,
    {
        output_arr.push((arr1[index] ^ arr2[index]));
        index += 1;
    }
    // proof block to assert the output_arr length
    proof {
        assert(arr1.len() == index); // Added by AI
        lemma_preserve_length_of_output(arr1@, output_arr@, index as int);
    }

    output_arr
}

} // verus!

// Score: Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1
// Safe: True