
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn find_first_occurrence(arr: &Vec<i32>, target: i32) -> (index: Option<usize>)
    requires
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
    ensures
        if let Some(idx) = index {
            &&& 0 <= idx < arr.len()
            &&& forall|k: int| 0 <= k < idx ==> arr[k] != target
            &&& arr[idx as int] == target
        } else {
            forall|k: int| 0 <= k < arr.len() ==> arr[k] != target
        },
{
    let mut index = 0;
    while index < arr.len()
        invariant 
            arr.len() == arr.len(),
            forall|k: int| 0 <= k < index ==> arr[k] != target,
            0 <= index <= arr.len(),
        decreases arr.len() - index, // Added by AI
    {
        if arr[index] == target {
            return Some(index);
        }
        index += 1;
    }
    proof {
        assert(forall|k: int| 0 <= k < arr.len() ==> arr[k] != target);
    }
    None
}

}

// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True