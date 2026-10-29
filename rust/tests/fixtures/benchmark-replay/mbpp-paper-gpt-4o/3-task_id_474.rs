
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
            index == result_str@.len(), // Corrected invariant: result_str's length is the current index
            forall|i: int|
                0 <= i < index ==> result_str[i] == (if str1[i] == old_char {
                    new_char
                } else {
                    str1[i]
                }),
        decreases str1.len() - index // Added by AI
    {
        if str1[index] == old_char {
            result_str.push(new_char);
        } else {
            result_str.push(str1[index]);
        }
        index += 1;
    }
    proof {
        assert(str1@.len() == result_str@.len()) by {
            // At the end of the loop, `index` == `str1.len()`, thus invariant `index == result_str@.len()` implies `result_str@.len() == str1.len()`.
            assert(index == str1.len());
            assert(index == result_str@.len());
        }
    }
    result_str
}

}

// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True