use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

proof fn valid_i64_to_i128_conversion(x: i64)
    ensures
        (x as i128) >= i128::MIN && (x as i128) <= i128::MAX
{
    assert((x as i128) >= i128::MIN && (x as i128) <= i128::MAX);
}

proof fn valid_sum_i64_to_i128_conversion(sum: i128, x: i64)
    ensures
        sum + (x as i128) >= i128::MIN && sum + (x as i128) <= i128::MAX
{
    valid_i64_to_i128_conversion(x);
    // additional assertion ensures sum and x within range don't overflow
    assert((sum + (x as i128) >= i128::MIN) && (sum + (x as i128) <= i128::MAX));
}

spec fn sum_to(arr: Seq<i64>) -> int
    decreases arr.len(),
{
    if arr.len() == 0 {
        0
    } else {
        sum_to(arr.drop_last()) + arr.last()
    }
}

fn sum(arr: &Vec<i64>) -> (sum: i128)
    ensures
        sum_to(arr@) == sum,
{
    let mut index = 0;
    let mut sum = 0i128;

    while index < arr.len()
        invariant forall |k: int| 0 <= k < arr.len() ==> arr@.index(k) == arr[k],
        decreases arr.len() - index,
    {
        proof {
            valid_sum_i64_to_i128_conversion(sum, arr[( index ) as int]);
            assert(sum + arr[(index) as int] as i128 >= i128::MIN && sum + arr[(index) as int] as i128 <= i128::MAX);
        }
        sum = sum + arr[index] as i128;
        index += 1;
    }
    
    proof {
        assert(sum_to(arr@) == sum); // Added by AI
    }

    sum
}

} // verus!
// Score: Compilation Error: False, Verified: 3, Errors: 2, Verus Errors: 2
// Safe: True