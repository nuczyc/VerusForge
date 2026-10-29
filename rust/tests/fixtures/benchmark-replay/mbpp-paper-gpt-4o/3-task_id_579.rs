
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
    decreases arr.len() - index
    {
        if (arr[index] == key) {
            return true;
        }
        index += 1;
    }
    false
}

proof fn assert_no_duplicates_in_variant(seq: Seq<i32>)
    ensures
        forall|i: int, j: int| 0 <= i < j < seq.len() ==> seq[i] != seq[j],
    decreases seq.len()
{
    if seq.len() > 0 {
        let last = seq.drop_last();
        assert_no_duplicates_in_variant(last);
        assert(forall|i: int| 0 <= i < last.len() ==> seq[i] != seq.last());
    }
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
    decreases arr1.len() - index
    {
        if (!contains(arr2, arr1[index]) && !contains(&result, arr1[index])) {
            result.push(arr1[index]);
        }
        index += 1;
    }
    let mut index = 0;
    while index < arr2.len()
    decreases arr2.len() - index
    {
        if (!contains(arr1, arr2[index]) && !contains(&result, arr2[index])) {
            result.push(arr2[index]);
        }
        index += 1;
    }
    proof {
        assert_no_duplicates_in_variant(result@);
        assert(forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j]);
        // Ensure the post-conditions
        assert(forall|i: int| 0 <= i < arr1.len() ==> (!arr2@.contains(arr1[i]) ==> result@.contains(arr1[i])));
        assert(forall|i: int| 0 <= i < arr2.len() ==> (!arr1@.contains(arr2[i]) ==> result@.contains(arr2[i])));
    }
    result
}

}

// Score: Compilation Error: False, Verified: 2, Errors: 5, Verus Errors: 5
// Safe: True