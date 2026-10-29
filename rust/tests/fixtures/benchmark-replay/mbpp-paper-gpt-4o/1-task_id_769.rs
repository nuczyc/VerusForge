
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
        invariant forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k]
        decreases arr.len() - index
    {
        if (arr[index] == key) {
            return true;
        }
        index += 1;
    }
    false
}

proof fn contains_forall(arr: &Vec<i32>, key: i32, r: bool)
    requires
        r == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
    ensures
        forall|i: int| 0 <= i < arr.len() ==> arr[i] == key ==> r,
{
    assert(r == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)));
}

proof fn set_difference_contains(arr1: &Vec<i32>, arr2: &Vec<i32>, index: usize)
    requires
        index < arr1.len(),
    ensures
        !arr2@.contains(arr1[( index ) as int]) ==> arr1@.contains(arr1[( index ) as int]),
{
    let val = arr1[( index ) as int];
    assert(!arr2@.contains(val));
    assert(arr1@.contains(val));
}

fn difference(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
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
        invariant
            forall |k: int| 0 <= k < arr1.len() ==> arr1[k] == arr1[k],
            forall|i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j],
            forall|i: int| 
                0 <= i < arr1.len() ==> (!arr2@.contains(#[trigger] arr1[i]) ==> result@.contains(arr1[i]))
        decreases arr1.len() - index
    {
        proof {
            set_difference_contains(arr1, arr2, index);
        }
        if (!contains(arr2, arr1[index]) && !contains(&result, arr1[index])) {
            result.push(arr1[index]);
        }
        index += 1;
    }
    index = 0;
    while index < arr2.len()
        invariant
            forall |k: int| 0 <= k < arr2.len() ==> arr2[k] == arr2[k],
            forall|i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j],
            forall|i: int| 
                0 <= i < arr1.len() ==> (!arr2@.contains(#[trigger] arr1[i]) ==> result@.contains(arr1[i])),
            forall|i: int| 
                0 <= i < arr2.len() ==> (!arr1@.contains(#[trigger] arr2[i]) ==> result@.contains(arr2[i]))
        decreases arr2.len() - index
    {
        if (!contains(arr1, arr2[index]) && !contains(&result, arr2[index])) {
            result.push(arr2[index]);
        }
        index += 1;
    }
    result
}

} // verus!

// Score: Compilation Error: False, Verified: 3, Errors: 4, Verus Errors: 4
// Safe: True