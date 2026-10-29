
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn square_nums(nums: &Vec<i32>) -> (squared: Vec<i32>)
    requires
        forall|k: int|
            0 <= k < nums.len() ==> (0 <= #[trigger] nums[k] * #[trigger] nums[k] < i32::MAX),
    ensures
        nums.len() == squared.len(),
        forall|k: int| 0 <= k < nums.len() ==> (#[trigger] squared[k] == nums[k] * nums[k]),
{
    let mut result: Vec<i32> = Vec::new();
    let mut index = 0;

    while index < nums.len()
        invariant
            // nums array is not modified in the loop, so invariants should cover every element
            forall|k: int| 0 <= k < nums.len() ==> (0 <= #[trigger] nums[k] * #[trigger] nums[k] < i32::MAX),
            nums.len() == nums.len(),
            result.len() <= nums.len(),
        decreases (nums.len() as i32) - (index as i32) // Added by AI
    {
        result.push(nums[index] * nums[index]);
        index += 1;
        proof {
    assert(0 <= index);  // Establish lower bound
    assert(0 <= index);  // Establish lower bound
    assert(0 <= index);  // Establish lower bound
            assert(result.len() <= index);
            assert(index <= nums.len());
        } // Added by AI
    }
    result
}

} // verus!
// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 2
// Safe: True