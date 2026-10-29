
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn contains_k(arr: &Vec<i32>, k: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == k)),
{
    let mut index = 0;
    while index < arr.len()
        invariant 
            arr.len() == arr.len(),
            !exists|i: int| 0 <= i < index && (arr[i] == k)
        decreases arr.len() - index
    {
        if (arr[index] == k) {
            return true;
        }
        index += 1;
    }
    proof {
        assert(!exists|i: int| 0 <= i < arr.len() && (arr[i] == k)); // This assertion is valid because of the loop invariant
    }
    false
}

} // verus!

// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True