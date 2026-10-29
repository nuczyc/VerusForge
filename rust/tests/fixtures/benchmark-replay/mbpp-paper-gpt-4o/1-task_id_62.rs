
use vstd::prelude::*;

fn main() {}

verus! {

fn smallest_num(nums: &Vec<i32>) -> (min: i32)
    requires
        nums.len() > 0,
    ensures
        forall|i: int| 0 <= i < nums.len() ==> min <= nums[i],
        exists|i: int| 0 <= i < nums.len() && min == nums[i],
{
    let mut min = nums[0];
    let mut index = 1;

    while index < nums.len() 
        invariant
            1 <= index <= nums.len(),
            min == nums[0] || (exists|j: int| 1 <= j < index && nums[j] == min),
            forall|k: int| 0 <= k < index ==> min <= nums[k],
        decreases nums.len() - index
    {
        if nums[index] < min {
            min = nums[index];
        }
        index += 1;
    }
    min
}

} // verus!

// Score: Compilation Error: False, Verified: 2, Errors: 0, Verus Errors: 0
// Safe: True