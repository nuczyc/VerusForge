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

proof fn u64_max_is_large()
    ensures
        u64::MAX >= 1_i64,
{
    // Proof by integer properties
    assert(u64::MAX == 18446744073709551615);
    assert(u64::MAX >= 1_i64);
}

proof fn count_true_assertion_helper(arr_len: usize, counter: u64)
    requires
        counter <= arr_len as u64,
    ensures
        counter < u64::MAX,
{
    u64_max_is_large();
    assert(u64::MAX > arr_len as u64);
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
            index <= arr.len(),
            counter >= 0, // Fixed by AI
            arr.len() == arr.len(),
            forall |k: int| 0 <= k < arr.len() ==> arr[k] ==> true, 
        decreases arr.len() - index, 
    {
        if (arr[index]) {
            proof {
                assert(counter <= arr.len() as u64);
                count_true_assertion_helper(arr.len(), counter);
            }
            assert(counter < u64::MAX);
            counter += 1;
        }
        index += 1;
    }
    counter
}

} // verus!
// Score: Compilation Error: False, Verified: 2, Errors: 4, Verus Errors: 4
// Safe: True