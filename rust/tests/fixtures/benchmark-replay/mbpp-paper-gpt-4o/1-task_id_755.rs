
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

spec fn min_spec(seq: Seq<i32>) -> int
    recommends
        0 < seq.len(),
    decreases seq.len(),
{
    if seq.len() == 1 {
        seq[0] as int
    } else if seq.len() == 0 {
        0
    } else {
        let later_min = min_spec(seq.drop_first());
        if seq[0] <= later_min {
            seq[0] as int
        } else {
            later_min as int
        }
    }
}

proof fn exists_second_min(numbers: Seq<i32>, min_index: usize, second_min_index: usize)
    requires
        numbers.len() >= 2,
        min_index < numbers.len(),
        second_min_index < numbers.len(),
        min_index != second_min_index,
        forall|k: int| 0 <= k < numbers.len() ==> numbers[k] >= numbers[( min_index ) as int],
        exists|k: int| 0 <= k < numbers.len() && k != min_index && (#[trigger] numbers[k] == numbers[( second_min_index ) as int]),
    ensures
        exists|k: int| 0 <= k < numbers.len() && k != min_index && numbers[k] == numbers[( second_min_index ) as int],
{
    // The existence condition is provided by the precondition, and thus met.
}

fn second_smallest(numbers: &Vec<i32>) -> (indices: (usize, usize))
    requires
        numbers.len() >= 2,
    ensures
        forall|k: int|
            0 <= k < numbers.len() && k != indices.0 && numbers[indices.0 as int] == min_spec(
                numbers@,
            ) ==> (#[trigger] numbers[k] >= numbers[indices.1 as int]),
        exists|k: int|
            0 <= k < numbers.len() && k != indices.0 && (#[trigger] numbers[k]
                == numbers[indices.1 as int]),
{
    let mut min_index: usize = 0;
    let mut second_min_index: usize = 1;

    if numbers[1] < numbers[0] {
        min_index = 1;
        second_min_index = 0;
    }
    let mut index = 2;
    while index < numbers.len()
        invariant
            numbers.len() == numbers.len(),
            0 <= index,
            0 <= min_index,
            min_index < numbers.len(),
            0 <= second_min_index,
            second_min_index < numbers.len(),
            exists|k: int| 0 <= k < index && k != min_index && numbers[k] == numbers[( second_min_index ) as int]
        decreases numbers.len() - index // Added by AI
    {
        if numbers[index] < numbers[min_index] {
            second_min_index = min_index;
            min_index = index;
        } else if numbers[index] < numbers[second_min_index] {
            second_min_index = index;
        }
        index += 1;
    }
    proof {
        exists_second_min(numbers@, min_index, second_min_index);
    }
    (min_index, second_min_index)
}

} // verus!





// Score: Compilation Error: False, Verified: 2, Errors: 3, Verus Errors: 3
// Safe: True