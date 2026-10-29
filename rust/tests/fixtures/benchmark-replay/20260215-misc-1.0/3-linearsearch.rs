
#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]
fn linear_search(nums: Vec<i32>, target: i32) -> (ret: i32)
requires
    nums@.len() < 0x8000_0000,
ensures
    ret < nums@.len(),
    ret >=0 ==> nums@[ret as int] == target,
    ret >=0 ==> forall |i: int| 0 <= i < ret as int ==> #[trigger]nums@[i] != target,
    ret < 0 ==> forall |i: int| 0 <= i < nums@.len() as int ==> #[trigger]nums@[i] != target,
{
    let mut i = 0;
    while i < nums.len()
    invariant
        nums@.len() < 0x8000_0000,
        nums.len() == nums.len(),
        nums@.len() == nums@.len(),
        forall |j: int| 0 <= j < i as int ==> nums@[j] != target, // added invariant
    decreases nums.len() - i
    {
        if nums[i] == target {
            proof {
                assert(nums@[i as int] == target); // Added by AI
            }
            break;
        }
        i = i + 1;
    }

    if i == nums.len() {
        proof {
            assert(forall |j: int| 0 <= j < nums@.len() as int ==> nums@[j] != target);
        }
        -1
    } else {
        proof {
            assert(i < nums@.len());
            assert(nums@[i as int] == target); // Added by AI
        }
        i as i32
    }
}
}

// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True