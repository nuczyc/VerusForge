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
        invariant 
            str.len() == (*str).len(),
            // str is never modified in the loop
            forall |k:int| 0 <= k < str.len() ==> str[k] == old(( str@[k] ) as &mut _)
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

    while index < arr1.len()
        invariant 
            arr1.len() == (*arr1).len(),
            arr2.len() == (*arr2).len(),
            output_str.len() <= arr1.len(),
            // arr1 and arr2 are never modified in the loop
            forall |k:int| 0 <= k < arr1.len() ==> arr1[k] == old(arr1@[k]),
            forall |k:int| 0 <= k < arr2.len() ==> arr2[k] == old(arr2@[k])
    {
        if (!contains(arr2, arr1[index])) {
            output_str.push(arr1[index]);
        }
        index += 1;
    }
    output_str
}

} // verus!

// Score: Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 3
// Safe: True