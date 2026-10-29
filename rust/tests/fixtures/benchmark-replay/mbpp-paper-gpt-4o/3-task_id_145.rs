use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

spec fn ensure_no_overflow(min_val: i32, max_val: i32) -> bool {
    max_val - min_val <= i32::MAX / 2 - i32::MIN / 2
}

proof fn lemma_monotonic_bounds(arr: &Vec<i32>, min_val: i32, max_val: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
        ensure_no_overflow(min_val, max_val),
    ensures
        ensure_no_overflow(min_val, max_val),
{
    // No code here; just a placeholder proof function.
}

proof fn lemma_max_min_bounds(min_val: i32, max_val: i32)
    requires
        min_val >= i32::MIN / 2,
        max_val <= i32::MAX / 2,
    ensures
        max_val - min_val >= i32::MIN / 2 - i32::MAX / 2,
{
    // Demonstrating the lower bound to support the assertion in main
}

fn max_difference(arr: &Vec<i32>) -> (diff: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
    ensures
        forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() ==> arr[i] - arr[j] <= diff,
{
    let mut min_val = arr[0];
    let mut max_val = arr[0];

    let mut index = 1;
    while index < arr.len()
    invariant
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
        forall|k: int| 0 <= k < arr.len() ==> arr[k] == arr[k],
        arr.len() == arr.len(),
        ensure_no_overflow(min_val, max_val),
    decreases arr.len() - index
    {
        if (arr[index] < min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }

        assert(ensure_no_overflow(min_val, max_val)) by {
            lemma_monotonic_bounds(arr, min_val, max_val);
        }
        
        index += 1;
    }

    proof {
        assert(min_val >= i32::MIN / 2);
    } // Added by AI
    assert(max_val - min_val >= i32::MIN / 2 - i32::MAX / 2) by {
        lemma_max_min_bounds(min_val, max_val);
    };
    assert(max_val - min_val <= i32::MAX / 2 - i32::MIN / 2); // No overflow

    max_val - min_val
}

} // verus!
// Score: Compilation Error: False, Verified: 1, Errors: 4, Verus Errors: 4
// Safe: True