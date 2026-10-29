
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

proof fn sum_within_bounds(x: i32, y: i32)
    requires
        i32::MIN / 2 <= x && x < i32::MAX / 2,
        i32::MIN / 2 <= y && y < i32::MAX / 2,
    ensures
        x + y > i32::MIN && x + y < i32::MAX,
{
    // Since both x and y are within half the bounds, their sum also remains within the bounds.
    let x_as_int = x as int;
    let y_as_int = y as int;
    
    assert(i32::MIN / 2 <= x_as_int && x_as_int < i32::MAX / 2);
    assert(i32::MIN / 2 <= y_as_int && y_as_int < i32::MAX / 2);

    assert(i32::MIN < x_as_int + y_as_int);
    assert(x_as_int + y_as_int < i32::MAX);
}

fn sum_min_max(arr: &Vec<i32>) -> (sum: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
    ensures
        sum == max_rcur(arr@) + min_rcur(arr@),
{
    let mut min_val = arr[0];
    let mut max_val = arr[0];
    let mut index = 1;

    while index < arr.len()
        invariant
            arr.len() > 0,
            forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
            arr.len() == arr.len(),
            forall|k: int| 0 <= k < arr.len() ==> i32::MIN / 2 < #[trigger] arr[k] < i32::MAX / 2,
        decreases arr.len() - index
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;
    }
    
    assert(i32::MIN / 2 <= max_val && max_val < i32::MAX / 2);
    assert(i32::MIN / 2 <= min_val && min_val < i32::MAX / 2);
    
    proof {
        sum_within_bounds(max_val, min_val);
    }
    
    max_val + min_val
}

} // verus!

// Score: Compilation Error: False, Verified: 2, Errors: 3, Verus Errors: 3
// Safe: True