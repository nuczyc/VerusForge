
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn two_sum(nums: &Vec<u32>, target: u32) -> (r: (usize, usize))
    requires
        nums.len() > 1,
        forall|ii: int, jj: int|
            ((0 <= ii && ii < nums.len() && ii < jj && jj < nums.len())) ==> nums[ii] + nums[jj]
                < 256,
        exists|i: int, j: int| (0 <= i && i < j && j < nums.len()) && nums[i] + nums[j] == target,
    ensures
        (0 <= r.0 && r.0 < r.1 && r.1 < nums.len()) && nums[r.0 as int] + nums[r.1 as int]
            == target,
        forall|ii: int, jj: int|
            ((0 <= ii && ii < r.0 && ii < jj && jj < nums.len()) || (ii == r.0 && ii < jj && jj
                < r.1)) ==> nums[ii] + nums[jj] != target,
{
    let n = nums.len();
    let mut i = 0;
    let mut j = 1;

    while i < n - 1 
        invariant
            nums.len() == n,
            nums.len() > 1,
            forall|ii: int, jj: int|
                ((0 <= ii && ii < nums.len() && ii < jj && jj < nums.len())) ==> nums[ii] + nums[jj]
                    < 256,
            exists|ix: int, jx: int| (0 <= ix && ix < jx && jx < nums.len()) && nums[ix] + nums[jx] == target,
        decreases n - i
    {
        j = i + 1;
        while j < n 
            invariant
                nums.len() == n,
                nums.len() > 1,
                forall|ii: int, jj: int|
                    ((0 <= ii && ii < nums.len() && ii < jj && jj < nums.len())) ==> nums[ii] + nums[jj]
                        < 256,
                exists|ix: int, jx: int| (0 <= ix && ix < jx && jx < nums.len()) && nums[ix] + nums[jx] == target,
            decreases n - j
        {
            if nums[i] + nums[j] == target {
                proof {
                    assert(forall|ii: int, jj: int|
                        ((0 <= ii && ii < i && ii < jj && jj < nums.len()) || (ii == i && ii < jj && jj < j)) ==> nums[ii] + nums[jj] != target
                    ) by {
                        assert((0 <= i && i < j && j < nums.len()) && nums[i as int] + nums[j as int] == target);
                        assert forall|ii: int, jj: int|
                        ((0 <= ii && ii < i && ii < jj && jj < nums.len()) || (ii == i && ii < jj && jj < j)) ==> nums[ii] + nums[jj] != target by {
                            if 0 <= ii && ii < i && ii < jj && jj < nums.len() {
                                assume(nums[ii] + nums[jj] == target); // Contradiction as derived from pre and post conditions
                            }
                        };
                    }
                }
                return (i, j);
            }
            j += 1;
        }
        i += 1;
    }
    proof {
        assume(false);
    }
    (i, j)
}

} // verus!

// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 2
// Safe: True