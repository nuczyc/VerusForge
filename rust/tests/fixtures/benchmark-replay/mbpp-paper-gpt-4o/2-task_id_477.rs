
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

proof fn check_len_equality(str_len: nat, lower_len: nat)
    requires
        lower_len == str_len,
    ensures
        lower_len == str_len,
{}

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
        invariant 
            forall |k: int| 0 <= k < str1.len() ==> str1[k] == str1[k],
            lower_case.len() == index,
            forall |j: int|
                0 <= j < index ==> lower_case[j] == (
                    if is_upper_case(str1[j]) {
                        shift32_spec(str1[j])
                    } else {
                        str1[j]
                    }
                ),
        decreases (str1.len() - index)
    {
        if (str1[index] >= 65 && str1[index] <= 90) {
            lower_case.push((str1[index] + 32) as u8);

        } else {
            lower_case.push(str1[index]);
        }
        index += 1;
    }
    proof {
        assert(lower_case@.len() == str1@.len());
        check_len_equality(str1@.len(), lower_case@.len());
    }
    lower_case
}

} // verus!

// Score: Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1
// Safe: True