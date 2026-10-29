
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn min_second_value_first(arr: &Vec<Vec<i32>>) -> (first_of_min_second: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2,
    ensures
        exists|i: int|
            0 <= i < arr.len() && first_of_min_second == #[trigger] arr[i][0] && (forall|j: int|
                0 <= j < arr.len() ==> (arr[i][1] <= #[trigger] arr[j][1])),
{
    let mut min_second_index = 0;
    let mut index = 0;

    while index < arr.len()
        invariant
            // Invariants for the array arr
            arr.len() > 0,
            forall|k: int| 0 <= k < arr.len() ==> arr[k].len() >= 2,
            // Invariants for the index - index is always in bounds since it starts at 0 and ends before arr.len()
            0 <= index <= arr.len(),
            // Invariant for min_second_index to ensure it's within bounds
            0 <= min_second_index < arr.len(),
            // Added invariant to ensure min_second_index maintains the minimum second value
            forall|j: int| 0 <= j < index ==> arr[( min_second_index ) as int][1] <= arr[j][1],
        decreases arr.len() - index,
    {
        if arr[index][1] < arr[min_second_index][1] {
            min_second_index = index;
        }
        index += 1;
    }
    proof {
    } // Added by AI
    arr[min_second_index][0]
}

} // verus!




// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True