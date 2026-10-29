
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn is_even_at_even_index(arr: &Vec<usize>) -> bool
    ensures
        result == forall|i: int| 0 <= i < arr.len() ==> ((i % 2) == (arr[i] % 2)),
{
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            forall|i: int| 0 <= i < index ==> ((i % 2) == (arr[i] % 2)), // Updated invariant
            arr.len() == arr.len(), // This invariant is kept as there is evidence that arr.len() doesn't change in the loop due to no arr.set() call
    {
        if ((index % 2) != (arr[index] % 2)) {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!

// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True