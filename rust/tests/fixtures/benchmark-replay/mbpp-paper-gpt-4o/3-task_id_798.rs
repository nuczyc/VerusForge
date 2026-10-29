
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

proof fn sum_safe_addition(x: i128, y: i128)
    requires
        x >= i128::MIN,
        x <= i128::MAX,
        y >= i128::MIN,
        y <= i128::MAX,
    ensures
        x + y >= i128::MIN && x + y <= i128::MAX,
{
    assert(x + y >= i128::MIN && x + y <= i128::MAX);
}

/// Helper function proving that sum accumulates the values in the sequence correctly
proof fn sum_accumulation(arr: Seq<i64>, index: int, sum: i128)
    requires
        sum_to(arr.subrange(0, index)) == sum,
    ensures
        sum_to(arr.subrange(0, index + 1)) == sum + arr[index as int],
{
    assert(sum_to(arr.subrange(0, index + 1)) == sum_to(arr.subrange(0, index)) + arr[index as int]);
}

fn sum(arr: &Vec<i64>) -> (sum: i128)
    ensures
        sum_to(arr@) == sum,
{
    let mut index = 0;
    let mut sum = 0i128;

    while index < arr.len()
        invariant
            sum_to(arr@.subrange(0, index as int)) == sum,
        decreases (arr.len() - index) as int,
    {
        // Assertion added to prevent overflow
        proof {
            sum_safe_addition(sum, arr[( index ) as int] as i128);
            sum_accumulation(arr@, index as int, sum);
        }

        assert(sum + arr[( index ) as int] as i128 >= i128::MIN && sum + arr[( index ) as int] as i128 <= i128::MAX);
        sum = sum + arr[index] as i128;
        index += 1;
    }

    proof {
        assert(sum_to(arr@.subrange(0, index as int)) == sum);
        assert(sum_to(arr@) == sum);
    }

    sum
}

} // verus!






// Score: Compilation Error: False, Verified: 2, Errors: 3, Verus Errors: 3
// Safe: True