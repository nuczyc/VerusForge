
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn max_difference(arr: &Vec<i32>) -> (diff: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
    ensures
        forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() ==> arr[i] - arr[j] <= diff,
{
    let mut min_val = arr[0];
    let mut max_val = arr[0];

    let mut index = 1;
    while index < arr.len() 
        invariant 
            arr.len() > 0,
            forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
            arr.len() == arr.len(),
            forall|k: int| 0 <= k < arr.len() ==> i32::MIN / 2 < #[trigger] arr[k] < i32::MAX / 2,
            i32::MIN / 2 < min_val < i32::MAX / 2,
            i32::MIN / 2 < max_val < i32::MAX / 2,
        decreases arr.len() - index
    {
        if (arr[index] < min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
    }

    assert(0 <= max_val);  // Establish lower bound
    assert(0 <= min_val);  // Establish lower bound
    assert(0 <= max_val);  // Establish lower bound
    assert(0 <= min_val);  // Establish lower bound
    assert(0 <= max_val);  // Establish lower bound
    assert(0 <= min_val);  // Establish lower bound
    assert(0 <= max_val);  // Establish lower bound
    assert(0 <= min_val);  // Establish lower bound
    assert(0 <= max_val);  // Establish lower bound
    assert(0 <= min_val);  // Establish lower bound
    assert(0 <= max_val);  // Establish lower bound
    assert(0 <= min_val);  // Establish lower bound
    assert(0 <= max_val);  // Establish lower bound
    assert(0 <= min_val);  // Establish lower bound
    assert(0 <= max_val);  // Establish lower bound
    assert(0 <= min_val);  // Establish lower bound
    assert(max_val >= min_val); // Ensures valid subtraction
    assert((max_val - min_val) <= (i32::MAX / 2 - i32::MIN / 2)); // Ensure no overflow
    max_val - min_val
}

} // verus!
// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 2
// Safe: True