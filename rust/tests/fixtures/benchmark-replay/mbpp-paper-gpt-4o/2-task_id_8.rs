
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
            nums.len() == nums.len(),
            result.len() == index,
            forall|k: int| 0 <= k < result.len() ==> (#[trigger] result[k] == nums[k] * nums[k]),
        decreases nums.len() - index,
    {
        result.push(nums[index] * nums[index]);
        index += 1;
    }
    
    proof {
        assert(nums.len() == index); // Changed from result.len() to index to ensure the correct lengths are compared.
    }
    result
}

} // verus!

// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True