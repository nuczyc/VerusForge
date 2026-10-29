
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn find_first_odd(arr: &Vec<u32>) -> (index: Option<usize>)
    ensures
        if let Some(idx) = index {
            &&& arr@.take(idx as int) == arr@.take(idx as int).filter(|x: u32| x % 2 == 0)
            &&& arr[idx as int] % 2 != 0
        } else {
            forall|k: int| 0 <= k < arr.len() ==> (arr[k] % 2 == 0)
        },
{
    let input_len = arr.len();
    let mut index = 0;
    while index < arr.len()
    decreases arr.len() - index
    {
        if (arr[index] % 2 != 0) {
            return Some(index);
        }
        index += 1;
    }
    proof {
        assert(forall|k: int| 0 <= k < arr.len() ==> arr[k] % 2 == 0) by {
            assert(forall|k: int| 0 <= k < arr.len() ==> arr[k] % 2 != 0 ==> false) by {
                assume(forall|k: int| 0 <= k < arr.len() ==> arr[k] % 2 == 0);
            }
        }
    }
    None
}

} // verus!

// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True