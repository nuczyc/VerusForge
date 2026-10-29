#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]
fn find_max(nums: Vec<i32>) -> (ret:i32)
requires
    nums.len() > 0,
ensures
    forall |i: int| 0 <= i < nums@.len() ==> nums@[i] <= ret,
    exists |i: int| 0 <= i < nums@.len() ==> nums@[i] == ret,
{
    let mut max = nums[0];
    let mut i = 1;
    while i < nums.len()
    invariant
        nums.len() > 0,
        nums.len() == nums.len(),
        forall |k: int| 0 <= k < nums.len() ==> nums[k] == nums@[k], // nums vector is not modified in this loop
        forall |k: int| 0 <= k < i ==> nums@[k] <= max, // Added by AI
        exists |j: int| 0 <= j < i && nums@[j] == max,
    decreases nums.len() - i
    {
        if nums[i] > max {
            max = nums[i];
        }
        i += 1;
    }
    proof {
        assert(exists |i: int| 0 <= i < nums@.len() ==> nums@[i] == max);
        assert(forall |i: int| 0 <= i < nums@.len() ==> nums@[i] <= max); // Added by AI
    }
    max
}
}

// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True