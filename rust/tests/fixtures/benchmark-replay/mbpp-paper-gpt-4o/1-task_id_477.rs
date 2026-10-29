
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

spec fn is_upper_case(c: u8) -> bool {
    c >= 65 && c <= 90
}

spec fn shift32_spec(c: u8) -> u8 {
    (c + 32) as u8
}

fn to_lowercase(str1: &[u8]) -> (result: Vec<u8>)
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> result[i] == (if is_upper_case(#[trigger] str1[i]) {
                shift32_spec(str1[i])
            } else {
                str1[i]
            }),
{
    let mut lower_case: Vec<u8> = Vec::with_capacity(str1.len());
    let mut index = 0;
    while index < str1.len()
        invariant str1.len() == str1.len(), lower_case.len() <= str1.len(),
            forall|k: int| 0 <= k < lower_case.len() ==> lower_case[k] == (if is_upper_case(#[trigger] str1[k]) {
                shift32_spec(str1[k])
            } else {
                str1[k]
            }),
        decreases (str1.len() - index)
    {
        if (str1[index] >= 65 && str1[index] <= 90) {
            lower_case.push((str1[index] + 32) as u8);

        } else {
            lower_case.push(str1[index]);
        }
        index += 1;

        proof {
            // This proof is for demonstrating that the invariant still holds after each iteration.
            // It shows the relationship between the elements in lower_case and str1.
            assert(forall|k: int| #![auto] 0 <= k < index ==> if is_upper_case(str1[k]) {
                shift32_spec(str1[k]) == lower_case[k]
            } else {
                str1[k] == lower_case[k]
            });
        }
    }
    lower_case
}

}

// Score: Compilation Error: False, Verified: 0, Errors: 4, Verus Errors: 4
// Safe: True