vstd::prelude::verus! {
    use vstd::prelude::*;

    fn main() {}

    fn two_sum(nums: & Vec < u32 >, target: u32) -> (r: (usize, usize))
        requires
            nums.len() > 1,
            forall | ii: int,
            jj: int |((0 <= ii && ii < nums.len() && ii < jj && jj < nums.len())) ==> nums[ii] + nums[jj] < 256,
            exists | i: int,
            j: int |(0 <= i && i < j && j < nums.len()) && nums[i] + nums[j] == target,
        ensures
            (0 <= r.0 && r.0 < r.1 && r.1 < nums.len()) && nums[r.0 as int] + nums[r.1 as int] == target,
            forall | ii: int,
            jj: int |((0 <= ii && ii < r.0 && ii < jj && jj < nums.len()) ||(ii == r.0 && ii < jj && jj < r.1)) ==> nums[ii] + nums[jj] != target,
    {
        let n = nums.len();
        let mut i = 0;
        let mut j = 1;
        while i < n - 1
            invariant
                true,
                nums.len() > 1,
                forall | ii: int,
                jj: int |((0 <= ii && ii < nums.len() && ii < jj && jj < nums.len())) ==> nums[ii] + nums[jj] < 256,
                exists | i: int,
                j: int |(0 <= i && i < j && j < nums.len()) && nums[i] + nums[j] == target,
                i <= n - 1,
                n == nums.len(),
                forall | ii: int,
                jj: int |(0 <= ii && ii < i && ii < jj && jj < n) ==> nums[ii] + nums[jj] != target,
            decreases
                n - 1 - i,
        {
            j = i + 1;
            while j < n
                invariant
                    true,
                    nums.len() > 1,
                    forall | ii: int,
                    jj: int |((0 <= ii && ii < nums.len() && ii < jj && jj < nums.len())) ==> nums[ii] + nums[jj] < 256,
                    exists | i: int,
                    j: int |(0 <= i && i < j && j < nums.len()) && nums[i] + nums[j] == target,
                    j <= n,
                    n == nums.len(),
                    i < n,
                    forall | ii: int,
                    jj: int |(0 <= ii && ii < i && ii < jj && jj < n) ==> nums[ii] + nums[jj] != target,
                    forall | jj: int |(i < jj && jj < j) ==> nums[i as int] + nums[jj] != target,
                decreases
                    n - j,
            {
                if nums[i] + nums[j] == target {
                    return(i, j);
                }
                j += 1;
            }
            i += 1;
        }
        (i, j)
    }
}

// Score: Compilation Error: False, Verified: 3, Errors: 1, Verus Errors: 1
// Safe: True
