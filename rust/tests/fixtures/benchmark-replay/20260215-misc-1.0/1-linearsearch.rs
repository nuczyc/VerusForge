
#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {

spec fn all_not_equal_up_to(nums: Seq<i32>, target: i32, len: nat) -> bool
    decreases len
{
    if len == 0 {
        true
    } else {
        nums[len - 1] != target && all_not_equal_up_to(nums, target, (len - 1) as nat)
    }
}

proof fn all_not_equal_implies_forall(nums: Seq<i32>, target: i32, len: nat)
    ensures
        all_not_equal_up_to(nums, target, len) ==> forall |i: int| 0 <= i < len ==> nums[i] != target,
    decreases len
{
    if len > 0 {
        all_not_equal_implies_forall(nums, target, (len - 1) as nat);
    }
}

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
        all_not_equal_up_to(nums@, target, (i) as nat),
    decreases (nums.len() - i) // Added by AI
    {
        if nums[i] == target {
            break;
        }
        i = i + 1;
    }
    proof {
        if i == nums.len() {
            assert(all_not_equal_up_to(nums@, target, nums@.len()));
            all_not_equal_implies_forall(nums@, target, nums@.len());
            assert(forall |i: int| 0 <= i < nums@.len() as int ==> #[trigger] nums@[i] != target);
        }
    }
    if i == nums.len() {
        proof {
            assert(forall |i: int| 0 <= i < nums@.len() as int ==> #[trigger] nums@[i] != target); // Added by AI
        }
        -1
    } else {
        proof {
            assert(nums@[i as int] == target);
            assert(forall |j: int| 0 <= j < i as int ==> #[trigger] nums@[j] != target);
        }
        i as i32
    }
}
}

// Score: Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 2
// Safe: True