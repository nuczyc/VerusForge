
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)
    ensures
        odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0),
{
    let mut odd_numbers: Vec<u32> = Vec::new();
    let input_len = arr.len();

    let mut index = 0;
    while index < arr.len()
        invariant
            arr.len() == input_len,
            odd_numbers.len() <= index,
            forall |j: int| 0 <= j < index ==> (arr[j] % 2 != 0) <==> (exists |k: int| 0 <= k < odd_numbers.len() && odd_numbers[k] == arr[j])
        // Added by AI
        decreases input_len - index
    {
        if (arr[index] % 2 != 0) {
            odd_numbers.push(arr[index]);
        }
        index += 1;
    }
    proof {
        assert(odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0)); // Added by AI
    }
    odd_numbers
}

} // verus!

// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 2
// Safe: True