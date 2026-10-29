
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn has_only_one_distinct_element(arr: &Vec<i32>) -> (result: bool)
    ensures
        result == (forall|i: int| 1 <= i < arr@.len() ==> arr[0] == #[trigger] arr[i]),
{
    if arr.len() <= 1 {
        return true;
    }
    let mut index = 1;
    while index < arr.len()
        invariant 
            1 <= index <= arr@.len(),
            forall|i: int| 1 <= i < index ==> arr[0] == #[trigger] arr[i], // invariant added
        decreases arr.len() - index
    {
        if arr[0] != arr[index] {
            return false;
        }
        index += 1;
    }
    proof {
        assert(forall|i: int| 1 <= i < arr@.len() ==> arr[0] == #[trigger] arr[i]);
    }
    true
}

} // verus!

// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True