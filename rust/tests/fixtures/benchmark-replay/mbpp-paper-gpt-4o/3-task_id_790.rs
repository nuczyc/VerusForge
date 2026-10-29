
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn is_even_at_even_index(arr: &Vec<usize>) -> (result: bool)
    ensures
        result == forall|i: int| 0 <= i < arr.len() ==> ((i % 2) == (arr[i] % 2)),
{
    let mut index = 0;
    while index < arr.len() 
        invariant
            0 <= index <= arr.len(),
            arr.len() == arr.len(),
            forall|i: int| 0 <= i < index ==> ((i % 2) == (arr[i] % 2)), // Correct invariant range
        decreases arr.len() - index, // Clarification on decreases clause
    {
        assert(forall|i: int| 0 <= i < index ==> ((i % 2) == (arr[i] % 2))); // Assertion about established range
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