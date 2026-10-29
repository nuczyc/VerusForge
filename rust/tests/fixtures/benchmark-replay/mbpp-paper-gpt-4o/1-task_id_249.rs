
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut i = 0;
    while i < arr.len()
        ensures
            arr.len() == old(( arr.len() ) as &mut _),
            forall |k:int| 0 <= k < arr.len() ==> arr[k] == old(( arr[k] ) as &mut _) // No arr.set() in the loop
    {
        if (arr[i] == key) {
            return true;
        }
        i += 1;
    }
    false
}

fn intersection(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (arr1@.contains(#[trigger] result[i]) && arr2@.contains(
                #[trigger] result[i],
            )),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    let mut output_arr = Vec::new();
    let mut index = 0;
    while index < arr1.len()
        ensures
            arr1.len() == old(( arr1.len() ) as &mut _),
            forall |k:int| 0 <= k < arr1.len() ==> arr1[k] == old(( arr1[k] ) as &mut _), // No arr1.set() in the loop
            arr2.len() == old(( arr2.len() ) as &mut _),
            forall |k:int| 0 <= k < arr2.len() ==> arr2[k] == old(arr2[k]), // No arr2.set() in the loop
            output_arr.len() <= old(arr1.len())
    {
        if (contains(arr2, arr1[index]) && !contains(&output_arr, arr1[index])) {
            output_arr.push(arr1[index]);
        }
        index += 1;
    }
    output_arr
}

} // verus!






// Score: Compilation Error: False, Verified: 0, Errors: 8, Verus Errors: 8
// Safe: True