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
            forall|i: int| 0 <= i < arr.len() ==> arr[i].len() > 0,
            first_elem_arr.len() == index,
            forall|j: int| 0 <= j < index ==> first_elem_arr[j] == arr[j][0],
        decreases arr.len() - index,
    {
        let seq = &arr[index];
        first_elem_arr.push(seq[0]);
        index += 1;
    }
    proof {
        // helper proof function invocation
        helper_first_elem_len(arr, first_elem_arr);
        assert(forall|i: int| 0 <= i < arr.len() ==> first_elem_arr[i] == arr[i][0]);
    }
    first_elem_arr
}

proof fn helper_first_elem_len(arr: &Vec<Vec<i32>>, first_elem_arr: Vec<i32>)
    ensures arr.len() == first_elem_arr.len()
{
    assert(arr.len() == first_elem_arr.len()); // Added by AI
}

} // verus!

// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1
// Safe: True