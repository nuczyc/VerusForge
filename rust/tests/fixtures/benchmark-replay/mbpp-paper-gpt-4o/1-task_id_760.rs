
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
            index >= 1,
            arr.len() > 1,
            arr.len() == arr.len(),
            forall |k: int| 0 <= k && k < arr.len() ==> arr[( index ) as int] == arr[( index ) as int], // Fixed by AI
        decreases arr.len() - index,
    {
        if arr[0] != arr[index] {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!



// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True