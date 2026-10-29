
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

proof fn u64_less_than_max(counter: int, seq_len: int)
    requires
        counter <= seq_len,
        seq_len < u64::MAX,
    ensures 
        counter < u64::MAX,
{
    assert(counter < u64::MAX);
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
            0 <= index <= arr.len(),
            count_boolean(arr@.subrange(0, index as int)) == counter,
        decreases arr.len() - index, 
    {
        if (arr[index]) {
            proof {
                count_boolean_upper_bound(arr@);
                u64_less_than_max(counter as int + 1, arr.len() as int);
            }
            assert(counter < u64::MAX);
            counter += 1;
        }
        index += 1;
    }
    counter
}

} // verus!

// Score: Compilation Error: False, Verified: 3, Errors: 4, Verus Errors: 4
// Safe: True