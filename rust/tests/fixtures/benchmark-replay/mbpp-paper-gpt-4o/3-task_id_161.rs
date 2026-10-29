
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut i = 0;
    while i < str.len()
        // No modifications to str in this loop, ensuring the invariant for all elements
        invariant forall|k: int| 0 <= k < str.len() ==> (exists|j: int| #[trigger] (j == i || str[j] != key)), // Fixed by AI
        decreases str.len() - i // Added by AI
    {
        if (str[i] == key) {
            return true;
        }
        i += 1;
    }
    false
}

fn remove_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (arr1@.contains(#[trigger] result[i]) && !arr2@.contains(
                #[trigger] result[i],
            )),
        forall|i: int|
            0 <= i < arr1.len() ==> (arr2@.contains(#[trigger] arr1[i]) || result@.contains(
                #[trigger] arr1[i],
            )),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;
    let ghost ghost_arr2_contains = Seq::new(( arr2.len() ) as nat, |i: int| arr2[i]); // Fixed by AI
    while index < arr1.len()
        // No modifications to arr1 in this loop, ensuring the invariant for all elements
        invariant forall|k: int| 0 <= k < arr1.len() ==> (arr2@.contains(#[trigger] arr1[k]) ==> ghost_arr2_contains.contains(#[trigger] arr1[k]) || output_str@.contains(#[trigger] arr1[k])), // Fixed by AI
        decreases arr1.len() as int - index as int // Added by AI
    {
        if (!contains(arr2, arr1[index])) {
            output_str.push(arr1[index]);
        }
        index += 1;
    }
    output_str
}

}

// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True