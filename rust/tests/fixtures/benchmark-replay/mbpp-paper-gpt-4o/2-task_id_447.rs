use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn cube_element(nums: &Vec<i32>) -> (cubed: Vec<i32>)
    requires
        forall|k: int|
            0 <= k < nums.len() ==> (i32::MIN <= #[trigger] nums[k] * #[trigger] nums[k]
                <= i32::MAX),
        forall|k: int|
            0 <= k < nums.len() ==> (i32::MIN <= #[trigger] nums[k] * #[trigger] nums[k]
                * #[trigger] nums[k] <= i32::MAX),
    ensures
        forall|i: int|
            0 <= i < nums.len() ==> cubed[i] == #[trigger] nums[i] * #[trigger] nums[i]
                * #[trigger] nums[i],
{
    let mut cubed_array: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < nums.len() 
        invariant 
            nums.len() == nums.len(), // Invariant specifying length of nums
            cubed_array.len() == i, // Invariant specifying length of cubed_array
            forall|j: int|
                0 <= j < i ==> cubed_array[j] == nums[j] * nums[j] * nums[j], // Maintain cubed correctness
            forall|k: int|
                0 <= k < nums.len() ==> (i32::MIN <= #[trigger] nums[k] * #[trigger] nums[k]
                <= i32::MAX), // nums is never changed in the loop
            forall|k: int|
                0 <= k < nums.len() ==> (i32::MIN <= #[trigger] nums[k] * #[trigger] nums[k]
                * #[trigger] nums[k] <= i32::MAX), // nums is never changed in the loop
        decreases nums.len() - i, // Decreases clause added by AI
    {
        cubed_array.push(nums[i] * nums[i] * nums[i]);
        i += 1;
    }
    cubed_array
}

} // verus!
// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True