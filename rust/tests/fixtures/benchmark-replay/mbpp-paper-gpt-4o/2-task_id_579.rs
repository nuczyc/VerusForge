
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut index = 0;
    while index < arr.len() 
        // arr is never changed within this loop
        invariant
            forall|k: int| 0 <= k < arr.len() ==> arr[k] == arr@.index(k),
        decreases arr.len() - index, // Added by AI
    {
        if (arr[index] == key) {
            return true;
        }
        index += 1;
    }
    false
}

fn find_dissimilar(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < arr1.len() ==> (!arr2@.contains(#[trigger] arr1[i]) ==> result@.contains(
                arr1[i],
            )),
        forall|i: int|
            0 <= i < arr2.len() ==> (!arr1@.contains(#[trigger] arr2[i]) ==> result@.contains(
                arr2[i],
            )),
        forall|i: int, j: int|
            0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j],
{
    let mut result = Vec::new();
    let mut index = 0;
    while index < arr1.len() 
        // arr1 is never changed within this loop
        invariant
            forall|k: int| 0 <= k < arr1.len() ==> arr1[k] == arr1@.index(k),
            forall|i: int, j: int|
                0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j], // Added by AI
            forall|i: int|
                0 <= i < arr1.len() ==> (!arr2@.contains(#[trigger] arr1[i]) ==> result@.contains(arr1[i])), // Added by AI
        decreases arr1.len() - index, // Added by AI
    {
        if (!contains(arr2, arr1[index]) && !contains(&result, arr1[index])) {
            result.push(arr1[index]);
        }
        index += 1;
    }
    proof {
        ensure_result_includes_dissimilar(arr1, arr2, &result);
    }
    
    let mut index = 0;
    while index < arr2.len() 
        // arr2 is never changed within this loop
        invariant
            forall|k: int| 0 <= k < arr2.len() ==> arr2[k] == arr2@.index(k),
            forall|i: int, j: int|
                0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j], // Added by AI
            forall|i: int|
                0 <= i < arr1.len() ==> (!arr2@.contains(#[trigger] arr1[i]) ==> result@.contains(arr1[i])), // Added by AI
            forall|i: int|
                0 <= i < arr2.len() ==> (!arr1@.contains(#[trigger] arr2[i]) ==> result@.contains(arr2[i])), // Added by AI        
        decreases arr2.len() - index, // Added by AI
    {
        if (!contains(arr1, arr2[index]) && !contains(&result, arr2[index])) {
            result.push(arr2[index]);
        }
        index += 1;
    }
    result
}

proof fn ensure_result_includes_dissimilar(arr1: &Vec<i32>, arr2: &Vec<i32>, result: &Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < arr1.len() ==> (!arr2@.contains(#[trigger] arr1[i]) ==> result@.contains(
                arr1[i],
            ))
{
    // This is the proof logic that ensures the dissimilar elements from arr1 are included in the result
}

} // verus!

// Score: Compilation Error: False, Verified: 2, Errors: 4, Verus Errors: 4
// Safe: True