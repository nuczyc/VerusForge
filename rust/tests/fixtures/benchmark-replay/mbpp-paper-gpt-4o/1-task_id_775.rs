use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn is_odd_at_odd_index(arr: &Vec<usize>) -> (result: bool)
    ensures
        result == forall|i: int| 0 <= i < arr.len() ==> ((i % 2) == (arr[i] % 2)),
{
    let mut index = 0;
    while index < arr.len()
        invariant 
            0 <= index <= arr.len(),
            forall|j: int| 0 <= j < index ==> (j % 2) == (arr[j] % 2), // Added by AI
        decreases arr.len() - index,
    {
        if ((index % 2) != (arr[index] % 2)) {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True