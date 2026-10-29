
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

spec fn is_lower_case(c: u8) -> bool {
    c >= 97 && c <= 122
}

spec fn shift_minus_32_spec(c: u8) -> u8 {
    (c - 32) as u8
}

fn to_uppercase(str1: &[u8]) -> (result: Vec<u8>)
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> (result[i] == (if is_lower_case(#[trigger] str1[i]) {
                shift_minus_32_spec(str1[i])
            } else {
                str1[i]
            })),
{
    let mut upper_case: Vec<u8> = Vec::with_capacity(str1.len());
    let mut index = 0;
    
    while index < str1.len()
        decreases str1.len() - index
    {
        if (str1[index] >= 97 && str1[index] <= 122) {
            upper_case.push((str1[index] - 32) as u8);
        } else {
            upper_case.push(str1[index]);
        }
        index += 1;
    }
    proof {
        lemma_upper_case_matches(str1, &upper_case);
    }
    upper_case
}

proof fn lemma_upper_case_matches(original: &[u8], result: &Vec<u8>)
    ensures
        original@.len() == result@.len(),
        forall|i: int|
            0 <= i < original.len() ==> (result[i] == (if is_lower_case(original[i]) {
                shift_minus_32_spec(original[i])
            } else {
                original[i]
            })),
{
    assert(original@.len() == result@.len());
    assert(forall|i: int| 
        0 <= i < original.len() ==> (result[i] == (if is_lower_case(original[i]) {
            shift_minus_32_spec(original[i])
        } else {
            original[i]
        })));
}
}

// Score: Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 2
// Safe: True