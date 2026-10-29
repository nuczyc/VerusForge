
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]
fn all_elements_equals(arr: &Vec<i32>, element: i32) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> (arr[i] == element)),
{
    let mut index = 0;
    while index < arr.len()
    invariant
        0 <= index <= arr.len(),
        arr.len() == arr.len(),
        forall|i: int| 0 <= i < index ==> (arr[i] == element), // Fixed by AI
    decreases arr.len() - index // Fixed by AI
    {
        if arr[index] != element {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!

// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True