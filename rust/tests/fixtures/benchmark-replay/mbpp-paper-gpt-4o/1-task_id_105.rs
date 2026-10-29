
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

spec fn count_boolean(seq: Seq<bool>) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_boolean(seq.drop_last()) + if (seq.last()) {
            1 as int
        } else {
            0 as int
        }
    }
}

proof fn count_boolean_upper_bound(seq: Seq<bool>)
    ensures
        count_boolean(seq) <= seq.len(),
    decreases seq.len()
{
    if seq.len() > 0 {
        count_boolean_upper_bound(seq.drop_last());
    }
}

fn count_true(arr: &Vec<bool>) -> (count: u64)
    ensures
        0 <= count <= arr.len(),
        count_boolean(arr@) == count,
{
    let mut index = 0;
    let mut counter = 0;

    while index < arr.len()
        invariant
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k],
            counter as usize <= arr.len(),
        decreases arr.len() - index,
    {
        if (arr[index]) {
            assert(counter < u64::MAX) by {
                count_boolean_upper_bound(arr@);
            };
            counter += 1;
        }
        index += 1;
    }
    counter
}

} // verus!

// Score: Compilation Error: False, Verified: 2, Errors: 4, Verus Errors: 4
// Safe: True