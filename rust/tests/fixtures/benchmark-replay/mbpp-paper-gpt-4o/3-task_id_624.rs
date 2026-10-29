
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

proof fn preserve_length_invariant(str_len: nat, index: nat, upper_case_len: nat)
    requires
        upper_case_len + (str_len - index) as int == str_len,
    ensures 
        str_len == upper_case_len + (str_len - index) as int,
{
    // This is trivially true given the requires clause.
}

proof fn final_length_invariant(str_len: nat, upper_case_len: nat)
    requires
        upper_case_len == str_len,
    ensures 
        str_len == upper_case_len,
{
    // This is trivially true given the requires clause.
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
        invariant
            str1@.len() == upper_case@.len() + (str1.len() - index) as int,
            forall|i: int|
                0 <= i < upper_case.len() ==> (upper_case[i] == (if is_lower_case(#[trigger] str1[i]) {
                    shift_minus_32_spec(str1[i])
                } else {
                    str1[i]
                })),
        decreases str1.len() - index
    {
        if (str1[index] >= 97 && str1[index] <= 122) {
            upper_case.push((str1[index] - 32) as u8);
        } else {
            upper_case.push(str1[index]);
        }
        index += 1;
        proof {
            preserve_length_invariant((str1.len()) as nat, index as nat, upper_case.len() as nat);
        }
    }
    proof {
        final_length_invariant(str1@.len(), upper_case@.len());
        assert(str1@.len() == upper_case@.len());
    }
    upper_case
}

}

// Score: Compilation Error: False, Verified: 3, Errors: 1, Verus Errors: 1
// Safe: True