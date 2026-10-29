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

proof fn lemma_sum_negative_to_property(seq: Seq<i64>, sum_neg: int, index: nat)
    requires
        index < seq.len(),
        sum_neg == sum_negative_to(seq.subrange(0, ( index ) as int)),
        seq.index(( index ) as int) < 0,
    ensures
        sum_neg + seq.index(( index ) as int) as int >= i64::MIN as int && sum_neg + seq.index(( index ) as int) as int <= i64::MAX as int
{
    lemma_sum_bounds(seq.subrange(0, ( index + 1 ) as int));
}

proof fn lemma_sum_bounds(seq: Seq<i64>)
    ensures
        sum_negative_to(seq) >= (i64::MIN as int) && sum_negative_to(seq) <= (i64::MAX as int),
    decreases seq.len()
{
    if seq.len() > 0 {
        // Recursively apply bounds
        lemma_sum_bounds(seq.drop_last());
    }
}

fn sum_negatives(arr: &Vec<i64>) -> (sum_neg: i128)
    ensures
        sum_negative_to(arr@) == sum_neg,
{
    let mut index = 0;
    let mut sum_neg = 0i128;

    while index < arr.len()
        invariant forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k],
        decreases arr.len() - index,
    {
        if (arr[index] < 0) {
            proof {
                let ghost_sum_neg: int = sum_negative_to(arr@.subrange(0, index as int)); // Added by AI
                assert(ghost_sum_neg == sum_neg); // Added by AI
            }
            assert(sum_neg + (arr[( index ) as int] as i128) >= (i64::MIN as i128) && sum_neg + (arr[( index ) as int] as i128) <= (i64::MAX as i128)) by {
                lemma_sum_negative_to_property(arr@, sum_neg as int, index as nat);
            };

            sum_neg = sum_neg + (arr[index] as i128);
        }
        index += 1;
    }
    sum_neg
}

} // verus!
// Score: Compilation Error: False, Verified: 1, Errors: 4, Verus Errors: 4
// Safe: True