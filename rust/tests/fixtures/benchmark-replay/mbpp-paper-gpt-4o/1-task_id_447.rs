
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
            nums.len() == nums.len(),
            cubed_array.len() <= i,
            i <= nums.len(),
            forall|k: int|
                0 <= k < nums.len() ==> (i32::MIN <= #[trigger] nums[k] * #[trigger] nums[k]
                    <= i32::MAX), // nums is never modified in the loop
            forall|k: int|
                0 <= k < nums.len() ==> (i32::MIN <= #[trigger] nums[k] * #[trigger] nums[k]
                    * #[trigger] nums[k] <= i32::MAX), // nums is never modified in the loop
            forall|j: int|
                0 <= j < i ==> cubed_array[j] == #[trigger] nums[j] * #[trigger] nums[j]
                    * #[trigger] nums[j],
        decreases nums.len() - i
    {
        cubed_array.push(nums[i] * nums[i] * nums[i]);
        i += 1;
        proof {
            assert(forall|j: int| 0 <= j < i - 1 ==> cubed_array[j] == #[trigger] nums[j] * #[trigger] nums[j] * #[trigger] nums[j]);
            assert(cubed_array[i - 1] == nums[i - 1] * nums[i - 1] * nums[i - 1]) by {
                let value = nums[i - 1]; // isolate value
                let cube = value * value * value; // compute cube
                assert(cubed_array[i - 1] == cube) by {
                    cube_element_computation(nums[i - 1]);
                };
            };
            assert(forall|j: int| 0 <= j < i ==> cubed_array[j] == #[trigger] nums[j] * #[trigger] nums[j] * #[trigger] nums[j]);
        }
    }
    cubed_array
}

proof fn cube_element_computation(value: i32)
    ensures
        value * value * value == value * value * value,
{
    // This is trivially true by the multiplicative identity
    // Showing that the cube math operation works as expected
}

}

// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2
// Safe: True