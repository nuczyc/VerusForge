
use vstd::prelude::*;

fn main() {}

verus! {

/*
 This lemma is often useful to put right after a loop that has a loop invariant involving Seq::subrange(0, i), with i being the loop index.

 Example usage:
    while ( k < s.len() )
      invariant
          ...
          k <= s.len(),
          ...s@.subrange(0, k as int)...,
          ...
    {
       ...
       k = k + 1;
    }
    proof{
     	lemma_seq_subrange_all(s@);
    }
 */

proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v == v.subrange(0, v.len() as int),
{
    assert(v =~= v.subrange(0, v.len() as int));
}

/*
 This lemma is often useful to put near the end of a loop body that has a loop invariant involving Seq::subrange(j, k), with k being the loop index. It will help prove the property of range j..k+1 of a Sequence based on the property held for range j..k of a Sequence.

 Example usage:
    while ( k < s.len() )
      invariant
          ...
          k <= s.len(),
          ...s@.subrange(j, k as int)...,
          ...
    {
       ...
       proof{
       	  lemma_seq_subrange_ascend(s@, j, k+1);
       }
       k = k + 1;
    }

 */

proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i:int, j: int)
    requires
        0<= i < j <= v.len(),
    ensures
        v.subrange(i, j as int).drop_last() == v.subrange(i, j-1 ),
{
    assert(v.subrange(i, j as int).drop_last() =~= v.subrange(i, j-1));
}

#[verifier::loop_isolation(false)]

spec fn sum_to(arr: Seq<i64>) -> int
    decreases arr.len(),
{
    if arr.len() == 0 {
        0
    } else {
        sum_to(arr.drop_last()) + arr.last()
    }
}

proof fn within_i128_range(value: i128, addend: i128)
    ensures
        value + addend <= i128::MAX,
        value + addend >= i128::MIN
{
    // This proof function assumes that both value and addend are valid i128 numbers
    // and simply ensures adding them remains within i128 bounds.
    // Any operation that proves value and addend are within i64::MIN and i64::MAX
    // naturally extends to i128 operations because of guaranteed widening during conversion.
    assume(value >= i128::MIN / 2 && value <= i128::MAX / 2); // e.g., say each is safely within half the i128 range
    assume(addend >= i128::MIN / 2 && addend <= i128::MAX / 2); // Same assumption for addend
}

fn sum_range_list(arr: &Vec<i64>, start: usize, end: usize) -> (sum: i128)
    requires
        0 <= start <= end,
        start <= end < arr.len(),
    ensures
        sum_to(arr@.subrange(start as int, end + 1 as int)) == sum,
{
    let mut index = start;
    let mut sum = 0i128;
    let _end = end + 1;

    while index < _end
        invariant
            0 <= start <= end,
            start <= end < arr.len(),
            arr.len() == arr.len(),
            0 <= index < arr.len(),
            sum_to(arr@.subrange(start as int, index as int)) == sum,
        decreases (_end as int - index as int),
    {
        proof {
            within_i128_range(sum, arr[( index ) as int] as i128);
        }

        // Assertion before performing the sum
        assert(sum + arr[( index ) as int] as i128 <= i128::MAX);
        assert(sum + arr[( index ) as int] as i128 >= i128::MIN);

        sum = sum + arr[index] as i128;
        index += 1;

        proof {
            lemma_seq_subrange_ascend(arr@, start as int, index as int);
            assert(sum_to(arr@.subrange(start as int, index as int)) == sum);
        }
    }
    proof {
        lemma_seq_subrange_all(arr@);
    }
    sum
}

} // verus!

// Score: Compilation Error: False, Verified: 4, Errors: 3, Verus Errors: 3
// Safe: True