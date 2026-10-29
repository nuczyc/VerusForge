use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut i = 0;
    let ghost arr_old = arr@; // Added by AI
    while i < arr.len()
        invariant forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr_old[k], // Fixed by AI
        decreases arr.len() - i // Added by AI
    {
        if (arr[i] == key) {
            return true;
        }
        i += 1;
    }
    false
}

fn shared_elements(list1: &Vec<i32>, list2: &Vec<i32>) -> (shared: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < shared.len() ==> (list1@.contains(#[trigger] shared[i]) && list2@.contains(
                #[trigger] shared[i],
            )),
        forall|i: int, j: int| 0 <= i < j < shared.len() ==> shared[i] != shared[j],
{
    let mut shared = Vec::new();
    let ghost list1_old = list1@; // Added by AI
    let mut index = 0;
    while index < list1.len()
        invariant forall |k: int| 0 <= k < list1.len() ==> list1[k] == list1_old[k], // Fixed by AI
        decreases list1.len() - index // Added by AI
    {
        if (contains(list2, list1[index]) && !contains(&shared, list1[index])) {
            shared.push(list1[index]);
        }
        index += 1
    }
    proof {
        assert(forall|i: int, j: int| 0 <= i < j < shared.len() ==> shared[i] != shared[j]); // Added by AI
    }
    shared
}

} // verus!
// Score: Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 3
// Safe: True