
#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]
spec fn seq_to_set_rec<A>(seq: Seq<A>) -> Set<A>
    decreases seq.len()
{
    if seq.len() == 0 {
        Set::empty()
    } else {
        seq_to_set_rec(seq.drop_last()).insert(seq.last())
    }
}


fn remove_duplicates(nums: Vec<i32>) -> (res: Vec<i32>)
ensures
    res@.no_duplicates(),
    nums@.to_set().ext_equal(res@.to_set())
{
    let mut res = Vec::new();
    let mut i = 0;
    while i < nums.len()
    {
        let mut found = false;
        let mut j = 0;

        while j < res.len()
        invariant
            /* The `nums` vector is not modified in this loop, hence we can ensure this invariant for all elements in `nums`: */
            forall |k: int| 0 <= k < nums.len() ==> nums[k] === nums@[k],
            forall |k: int| 0 <= k < res.len() ==> res[k] === res@[k]
        {
            if nums[i] == res[j] {
                found = true;
                break;
            }
            j += 1;
        }
        
        if !found {
            res.push(nums[i]);
        }
        i += 1;
    }
    res
}
}
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True