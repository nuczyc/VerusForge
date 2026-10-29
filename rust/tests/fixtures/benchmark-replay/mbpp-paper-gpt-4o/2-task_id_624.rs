
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

proof fn lemma_index_le_len(index: nat, len: nat)
    requires 
        index <= len,
    ensures
        index <= len
{}

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
            str1.len() == str1.len(),
            upper_case.len() == index,
            forall|k: int| 0 <= k < index ==> upper_case[k] == (if is_lower_case(str1[k]) { shift_minus_32_spec(str1[k]) } else { str1[k] })
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
        assert(upper_case.len() == index);
        assert(forall|k: int| 0 <= k < index ==> upper_case[k] == (if is_lower_case(str1[k]) { shift_minus_32_spec(str1[k]) } else { str1[k] }));
        assert(index == str1.len()) by {
            lemma_index_le_len(index as nat, str1.len() as nat);
            assert(index <= str1.len());
        };
        assert(upper_case.len() == str1.len());
    }
    upper_case
}

} // verus!

// Score: Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1
// Safe: True