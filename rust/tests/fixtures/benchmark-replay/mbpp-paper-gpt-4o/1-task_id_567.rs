use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn is_sorted(arr: &Vec<i32>) -> (is_sorted: bool)
    requires
        arr.len() > 0,
    ensures
        is_sorted == (forall|i: int, j: int| 0 <= i < j < arr.len() ==> (arr[i] <= arr[j])),
{
    let mut index = 0;
    while index < arr.len() - 1
        invariant
            arr.len() > 0,
            arr.len() == arr.len(),
            forall |k: int| 0 <= k < arr.len() ==> (arr[k] == arr[k]), // Fixed by AI
            forall|i: int, j: int| 0 <= i < j <= index ==> (arr[i] <= arr[j]), // Added by AI
        decreases
            arr.len() - index
    {
        if arr[index] > arr[index + 1] {
            return false;
        }
        index += 1;
    }
    proof {
        assert(forall|i: int, j: int| 0 <= i < j < arr.len() ==> (arr[i] <= arr[j]));
    }
    true
}

} // verus!
// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True