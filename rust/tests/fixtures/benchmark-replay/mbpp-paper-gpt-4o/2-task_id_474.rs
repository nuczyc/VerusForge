
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]
fn replace_chars(str1: &[u8], old_char: u8, new_char: u8) -> (result: Vec<u8>)
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> result[i] == (if str1[i] == old_char {
                new_char
            } else {
                str1[i]
            }),
{
    let mut result_str = Vec::with_capacity(str1.len());
    let mut index = 0;
    while index < str1.len()
    invariant
        0 <= index <= str1.len(),
        forall |k: int| 0 <= k < index ==> result_str[k] == (if str1[k] == old_char { new_char } else { str1[k] }),
    decreases
        str1.len() - index,
    {
        if str1[index] == old_char {
            result_str.push(new_char);
        } else {
            result_str.push(str1[index]);
        }
        index += 1;
        proof {
            if index > 1 {
                assert(forall |k: int| 0 <= k < index - 1 ==> result_str[k] == (if str1[k] == old_char { new_char } else { str1[k] }));
                assert_invariant_maintained(str1, old_char, new_char, &result_str, index);
            }
        }
    }
    result_str
}

proof fn assert_invariant_maintained(str1: &[u8], old_char: u8, new_char: u8, result_str: &Vec<u8>, index: usize)
    requires
        0 <= index <= str1.len(),
        forall |k: int| 0 <= k < index - 1 ==> result_str[k] == (if str1[k] == old_char { new_char } else { str1[k] })
    ensures
        forall |k: int| 0 <= k < index ==> result_str[k] == (if str1[k] == old_char { new_char } else { str1[k] })
{
    let k = index - 1;
    assert(forall |j: int| 0 <= j < index - 1 ==> result_str[j] == (if str1[j] == old_char { new_char } else { str1[j] }));
    assert(result_str[k] == (if str1[k] == old_char { new_char } else { str1[k] }));
}

}

// Score: Compilation Error: False, Verified: 0, Errors: 4, Verus Errors: 4
// Safe: True