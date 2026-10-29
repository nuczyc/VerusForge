
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

spec fn sum_negative_to(seq: Seq<i64>) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        sum_negative_to(seq.drop_last()) + if (seq.last() < 0) {
            seq.last() as int
        } else {
            0 as int
        }
    }
}

fn sum_negatives(arr: &Vec<i64>) -> (sum_neg: i128)
    ensures
        sum_negative_to(arr@) == sum_neg,
{
    let mut index = 0;
    let mut sum_neg = 0i128;

    while index < arr.len()
        invariant forall |k: int| 0 <= k < arr.len() ==> arr@[k] == arr@[k],
        decreases arr.len() - index, // Added by AI
    {
        if (arr[index] < 0) {
            sum_neg = sum_neg + (arr[index] as i128);
        }
        index += 1;

    }
    sum_neg
}
}

// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2
// Safe: True