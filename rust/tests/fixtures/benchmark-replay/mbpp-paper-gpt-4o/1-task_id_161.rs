
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
        invariant 0 <= i <= str.len(),
        decreases str.len() - i,
    {
        if (str[i] == key) {
            return true;
        }
        i += 1;
    }
    false
}

proof fn arr1_elements_in_arr2_or_output(arr1: &Vec<i32>, arr2: &Vec<i32>, output_str: &Vec<i32>)
    ensures forall|i: int| 
        0 <= i < arr1.len() ==> (arr2@.contains(arr1[i]) || output_str@.contains(arr1[i]))
{
    assert(forall|i: int| {
        0 <= i < arr1.len() ==> (arr2@.contains(arr1[i]) || output_str@.contains(arr1[i]))
    });
}

proof fn elements_are_in_arr1_not_in_arr2(arr1: &Vec<i32>, arr2: &Vec<i32>, output_str: &Vec<i32>)
    ensures forall|i: int| 
        0 <= i < output_str.len() ==> (arr1@.contains(output_str[i]) && !arr2@.contains(output_str[i]))
{
    assert(forall|i: int| {
        0 <= i < output_str.len() ==> (arr1@.contains(output_str[i]) && !arr2@.contains(output_str[i]))
    });
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
        invariant 0 <= index <= arr1.len(),
        decreases arr1.len() - index,
    {
        if (!contains(arr2, arr1[index])) {
            output_str.push(arr1[index]);
        }
        index += 1;
    }

    proof {
        arr1_elements_in_arr2_or_output(arr1, arr2, &output_str);
        elements_are_in_arr1_not_in_arr2(arr1, arr2, &output_str);

        assert(forall|i: int| 
            0 <= i < output_str.len() ==> (arr1@.contains(output_str[i]) && !arr2@.contains(output_str[i])));
    }
    
    output_str
}

}

// Score: Compilation Error: False, Verified: 2, Errors: 3, Verus Errors: 3
// Safe: True