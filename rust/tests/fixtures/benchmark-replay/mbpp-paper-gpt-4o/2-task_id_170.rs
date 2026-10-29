use vstd::prelude::*;

fn main() {}

verus! {

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


proof fn lemma_monotonic(arr: Seq<i64>, i: nat, j: nat)
    requires
        i <= j && j < arr.len() as nat,
    ensures
        sum_to(arr.subrange(0, ( i ) as int)) <= sum_to(arr.subrange(0, ( j+1 ) as int)),
    decreases j - i
{
    if i < j {
        lemma_monotonic(arr, i, (j-1) as nat);
    }
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
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k], // The array `arr` is never changed in the loop
            sum + arr[( index ) as int] as i128 <= i128::MAX, // Added by AI
            sum + arr[( index ) as int] as i128 >= i128::MIN, // Added by AI
        decreases _end - index
    {
        proof {
            assert(start <= index && index < arr.len() as nat);
            assert(i128::MIN <= arr[( index ) as int] as i128 && arr[( index ) as int] as i128 <= i128::MAX); // Added by AI
        }
        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!


// Score: Compilation Error: False, Verified: 1, Errors: 4, Verus Errors: 4
// Safe: True