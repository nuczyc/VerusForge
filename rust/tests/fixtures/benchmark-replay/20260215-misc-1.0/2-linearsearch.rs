
#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {

proof fn target_found_in_seq(nums: Seq<i32>, target: i32, i: int)
    requires
        0 <= i < nums.len(),
        nums[i] == target,
    ensures
        nums[i] == target,
{}

proof fn target_not_found_in_seq(nums: Seq<i32>, target: i32, len: int)
    requires
        len == nums.len(),
        forall |i: int| 0 <= i < len ==> #[trigger] nums[i] != target,
    ensures
        forall |i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] != target,
{}

#[verifier::loop_isolation(false)]
fn linear_search(nums: Vec<i32>, target: i32) -> (ret: i32)
requires
    nums@.len() < 0x8000_0000,
ensures
    ret < nums@.len(),
    ret >= 0 ==> nums@[ret as int] == target,
    ret >= 0 ==> forall |i: int| 0 <= i < ret as int ==> #[trigger] nums@[i] != target,
    ret < 0 ==> forall |i: int| 0 <= i < nums@.len() as int ==> #[trigger] nums@[i] != target,
{
    let mut i = 0;
    while i < nums.len()
    invariant
        nums@.len() < 0x8000_0000,
        nums.len() == nums.len(),
        forall |k: int| 0 <= k < i ==> #[trigger] nums@[k] != target,
    decreases nums.len() - i,
    {
        if nums[i] == target {
            break;
        }
        i = i + 1;
    }
    if i == nums.len() {
        proof {
            assert(forall |k: int| 0 <= k < nums@.len() ==> #[trigger] nums@[k] != target);
            target_not_found_in_seq(nums@, target, nums@.len() as int);
        }
        -1
    } else {
        proof {
            target_found_in_seq(nums@, target, i as int);
            assert(nums@[i as int] == target);
        }
        i as i32
    }
}
}

// Score: Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 2
// Safe: True