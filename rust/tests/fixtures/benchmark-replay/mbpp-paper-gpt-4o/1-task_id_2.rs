
use vstd::prelude::*;

fn main() {}

verus! {

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut i = 0;
    while i < arr.len()
        invariant
            forall|k: int| 0 <= k < arr.len() ==> arr[k] == arr[k],
            !exists|k: int| 0 <= k < i && arr[k] == key
        decreases arr.len() - i
    {
        if (arr[i] == key) {
            proof {
                lemma_exists_key(arr, key, i);
            }
            return true;
        }
        i += 1;
    }
    proof {
        lemma_not_exists_key(arr, key);
    }
    false
}

proof fn lemma_exists_key(arr: &Vec<i32>, key: i32, index: usize)
    requires 0 <= index < arr.len(), arr[( index ) as int] == key
    ensures exists|i: int| 0 <= i < arr.len() && arr[i] == key
{}

proof fn lemma_not_exists_key(arr: &Vec<i32>, key: i32)
    ensures !exists|i: int| 0 <= i < arr.len() && (arr[i] == key)
{
    assert(forall|i: int| 0 <= i < arr.len() ==> (arr[i] != key));
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
    let mut index = 0;
    while index < list1.len()
        invariant
            forall|i: int|
                0 <= i < shared.len() ==> (list1@.contains(#[trigger] shared[i]) && list2@.contains(#[trigger] shared[i])),
            forall|i: int, j: int| 0 <= i < j < shared.len() ==> shared[i] != shared[j]
        decreases list1.len() - index
    {
        if (contains(list2, list1[index]) && !contains(&shared, list1[index])) {
            shared.push(list1[index]);
        }
        index += 1
    }
    shared
}

} // verus!


// Score: Compilation Error: False, Verified: 5, Errors: 1, Verus Errors: 1
// Safe: True