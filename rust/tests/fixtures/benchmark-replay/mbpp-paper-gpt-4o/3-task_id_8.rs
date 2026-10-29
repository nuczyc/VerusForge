
use vstd::prelude::*;

fn main() {}

verus! {

proof fn length_preserved(nums: &Vec<i32>, result: &Vec<i32>, index: usize)
    requires
        nums.len() == result.len() + (nums.len() - index),
    ensures
        nums.len() == index + result.len()
{
    let remaining_len = nums.len() - index;
    assert(nums.len() == remaining_len + result.len());
    assert(result.len() == nums.len() - remaining_len);
    assert(nums.len() == index + result.len());
}

proof fn lemma_length_preserved(nums: &Vec<i32>, result: &Vec<i32>, index: usize)
    requires
        nums.len() == result.len() + (nums.len() - index),
    ensures
        nums.len() == index + result.len()
{
    length_preserved(nums, result, index);
}

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
            forall|k: int| 0 <= k < index ==> (#[trigger] result[k] == nums[k] * nums[k]),
            nums.len() == result.len() + (nums.len() - index),
            forall|k: int| 0 <= k < nums.len() ==> (0 <= #[trigger] nums[k] * #[trigger] nums[k] < i32::MAX),
        decreases nums.len() - index
    {
        result.push(nums[index] * nums[index]);
        index += 1;
    }

    proof {
        lemma_length_preserved(nums, &result, index);
        assert(nums.len() == index + result.len());
    }
    
    result
}

} // verus!

// Score: Compilation Error: False, Verified: 3, Errors: 1, Verus Errors: 1
// Safe: True