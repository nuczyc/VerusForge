
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn list_deep_clone(arr: &Vec<u64>) -> (copied: Vec<u64>)
    ensures
        arr@.len() == copied@.len(),
        forall|i: int| (0 <= i < arr.len()) ==> arr[i] == copied[i],
{
    let mut copied_array = Vec::with_capacity(arr.len());
    let mut index = 0;
    while index < arr.len()
        invariant
            copied_array.len() == index,
            index <= arr.len(),
            forall|k: int| 0 <= k < index ==> arr[k] == copied_array[k],
        decreases arr.len() - index, // Added by AI
    {
        copied_array.push(arr[index]);
        index += 1;
    }
    copied_array
}

} // verus!

// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True