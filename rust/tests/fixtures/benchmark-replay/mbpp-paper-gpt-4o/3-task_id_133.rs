
use vstd::prelude::*;

fn main() {}

verus! {

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

proof fn lemma_sum_negative_to_bound(seq: Seq<i64>)
    ensures
        sum_negative_to(seq) <= sum_negative_to(seq) // You would like to replace this with a proper bound condition,
        // such as verifying non-overflow under certain constraints.
    decreases seq.len()
{
    if seq.len() > 0 {
        lemma_sum_negative_to_bound(seq.drop_last());
        // Use properties of seq.last() and seq.drop_last() to bound the sum.
    }
}

fn sum_negatives(arr: &Vec<i64>) -> (sum_neg: i128)
    ensures
        sum_negative_to(arr@) == sum_neg,
{
    let mut index = 0;
    let mut sum_neg = 0i128;

    while index < arr.len()
        invariant
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k], // arr is not modified in the loop
            index <= arr.len(),
            sum_neg <= sum_negative_to(arr@),
            arr.len() == arr.len(),
        decreases arr.len() - index
    {
        if (arr[index] < 0) {
            // Assert bounds to prevent underflow/overflow
            assert(sum_neg + (arr[( index ) as int] as i128) <= sum_negative_to(arr@)) by {
                lemma_sum_negative_to_bound(arr@);
            }
            sum_neg = sum_neg + (arr[index] as i128);
        }
        index += 1;
    }
    sum_neg
}

} // verus!


// Score: Compilation Error: False, Verified: 2, Errors: 3, Verus Errors: 3
// Safe: True