
#![verifier::loop_isolation(false)]
use vstd::math::*;
use vstd::prelude::*;

fn main() {}

verus! {

spec fn max_rcur(seq: Seq<i32>) -> int
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        max(seq.last() as int, max_rcur(seq.drop_last()))
    }
}

spec fn min_rcur(seq: Seq<i32>) -> int
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        min(seq.last() as int, min_rcur(seq.drop_last()))
    }
}

proof fn lemma_max_min_monotonic(seq: Seq<i32>)
    ensures
        max_rcur(seq) >= min_rcur(seq),
{
    if seq.len() > 1 {
        let last_elem = seq.last() as int;
        let rest = seq.drop_last();
        assert(max_rcur(rest) >= min_rcur(rest));
        assert(max_rcur(seq) >= min_rcur(seq));
    }
}

fn difference_max_min(arr: &Vec<i32>) -> (diff: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
    ensures
        diff == max_rcur(arr@) - min_rcur(arr@),
{
    let mut min_val = arr[0];
    let mut max_val = arr[0];
    let mut index = 1;

    while index < arr.len()
        invariant
            arr.len() == arr.len(),
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k],
        decreases arr.len() - index,
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
    }

    // Assertion to verify that the max and min difference won't overflow/underflow
    assert(max_rcur(arr@) >= min_rcur(arr@)) by {
        lemma_max_min_monotonic(arr@);
    }

    assert(max_val as int - min_val as int >= 0);
    assert(max_val as int - min_val as int <= i32::MAX as int);

    max_val - min_val
}

} // verus!

// Score: Compilation Error: False, Verified: 3, Errors: 2, Verus Errors: 2
// Safe: True