
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

proof fn calculate_bounds(a: i32, b: i32)
    requires
        i32::MIN / 2 < a < i32::MAX / 2,
        i32::MIN / 2 < b < i32::MAX / 2,
    ensures
        a as int - b as int >= i32::MIN as int,
        a as int - b as int <= i32::MAX as int,
{
    // Calculate bounds using the properties of integers, ensuring a-b falls within i32 range
    assert(i32::MIN as int <= i32::MIN / 2 as i32 - i32::MAX / 2 as i32);
    assert(i32::MAX / 2 as i32 - i32::MIN / 2 as i32 <= i32::MAX as int);
}

/// Helper proof to ensure min_val and max_val maintain their bounds throughout the loop
proof fn maintain_bounds(min_val: i32, max_val: i32)
    requires
        i32::MIN / 2 < min_val < i32::MAX / 2,
        i32::MIN / 2 < max_val < i32::MAX / 2,
    ensures
        i32::MIN / 2 < min_val < i32::MAX / 2,
        i32::MIN / 2 < max_val < i32::MAX / 2,
{
    // Trivial proof as the values are maintained within the loop with no external modification
}

proof fn assert_value_bounds(val: i32)
    requires
        i32::MIN / 2 < val < i32::MAX / 2,
{
    assert(i32::MIN / 2 < val < i32::MAX / 2);
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
            arr.len() > 0,
            forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
            min_val <= max_val,
            arr.len() == arr.len(),
        decreases arr.len() - index,
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
            proof {
                assert_value_bounds(min_val);
            }
        } else if (arr[index] > max_val) {
            max_val = arr[index];
            proof {
                assert_value_bounds(max_val);
            }
        }
        proof {
            maintain_bounds(min_val, max_val);
        }
        index += 1;
    }
    
    proof {
        assert_value_bounds(max_val);
        assert_value_bounds(min_val);
    }
    proof {
        assert(i32::MIN / 2 < max_val < i32::MAX / 2);
        assert(i32::MIN / 2 < min_val < i32::MAX / 2);
    } // Added by AI
    proof {
        calculate_bounds(max_val, min_val);
    }
    
    assert(max_val as int - min_val as int >= i32::MIN as int && max_val as int - min_val as int <= i32::MAX as int);

    max_val - min_val
}

} // verus!

// Score: Compilation Error: False, Verified: 5, Errors: 2, Verus Errors: 2
// Safe: True