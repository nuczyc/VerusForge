
use vstd::prelude::*;

fn main() {}

verus! {

fn get_first_elements(arr: &Vec<Vec<i32>>) -> (result: Vec<i32>)
    requires
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() > 0,
    ensures
        arr.len() == result.len(),
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] result[i] == #[trigger] arr[i][0],
{
    let mut first_elem_arr: Vec<i32> = Vec::new();
    let mut index = 0;
    while index < arr.len() 
        invariant
            0 <= index <= arr.len(),
            first_elem_arr.len() == index,
            forall|j: int| 0 <= j < index ==> first_elem_arr[j] == #[trigger] arr[j][0],
            forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() > 0,
            forall|i: int| 0 <= i < arr.len() ==> arr[i].len() > 0, // No arr.set() in the loop, invariant should cover all elements
            arr.len() == arr.len(),
            first_elem_arr.len() == first_elem_arr.len(),
        decreases (arr.len() as int - index)
    {
        let seq = &arr[index];
        first_elem_arr.push(seq[0]);
        index += 1;
    }
    first_elem_arr
}

} // verus!

// Score: Compilation Error: False, Verified: 2, Errors: 0, Verus Errors: 0
// Safe: True