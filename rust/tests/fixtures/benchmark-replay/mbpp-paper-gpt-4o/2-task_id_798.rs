
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

proof fn ensure_no_overflow(val: i64, current_sum: i128) 
    ensures
        current_sum + val as i128 <= i128::MAX,
        current_sum + val as i128 >= i128::MIN,
{
    assert(val as i128 <= i128::MAX);
    assert(val as i128 >= i128::MIN);
}

proof fn sum_to_eq_accumulate(arr: Seq<i64>, index: int, sum: int) // Fixed by AI
    ensures
        sum_to(arr.subrange(0, index as int)) == sum,
    decreases index
{
    if index > 0 {
        sum_to_eq_accumulate(arr, index - 1, sum - arr[(index - 1) as int]);
    } else {
        assert(sum_to(arr.subrange(0, index as int)) == 0);
    }
}

fn sum(arr: &Vec<i64>) -> (sum: i128)
    ensures
        sum_to(arr@) == sum,
{
    let mut index = 0;
    let mut sum = 0i128;

    while index < arr.len()
        decreases arr.len() - index 
    {
        // Ensuring sum doesn't overflow
        proof {
            ensure_no_overflow(arr[( index ) as int], sum);
        }
        assert(sum + arr[( index ) as int] as i128 <= i128::MAX && sum + arr[( index ) as int] as i128 >= i128::MIN);
        
        sum = sum + arr[index] as i128;
        index += 1;
    }

    proof {
        sum_to_eq_accumulate(arr@, ( arr.len() ) as int, sum as int); // Fixed by AI
        assert(sum_to(arr@) == sum as int); // Fixed by AI
    }
    
    sum
}

} // verus!


// Score: Compilation Error: False, Verified: 2, Errors: 5, Verus Errors: 5
// Safe: True