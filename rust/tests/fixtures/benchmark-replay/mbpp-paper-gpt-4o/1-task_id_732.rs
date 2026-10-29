use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

spec fn is_space_comma_dot_spec(c: u8) -> bool {
    (c == 32) || (c == 44) || (c == 46)
}

proof fn result_len_invariant(str1_len: usize, result_len: usize) 
    ensures
        result_len <= str1_len,
{
    // Given that `index <= str1.len()` and every loop iteration adds at most one element
    // to `result`, the invariant `result.len() <= str1.len()` holds at all times.
}

fn replace_with_colon(str1: &[u8]) -> (result: Vec<u8>)
    ensures
        str1@.len() == result@.len(),
        forall|k: int|
            0 <= k < result.len() ==> #[trigger] result[k] == (if is_space_comma_dot_spec(str1[k]) {
                58
            } else {
                str1[k]
            }),
{
    let mut result: Vec<u8> = Vec::with_capacity(str1.len());
    let mut index = 0;
    while index < str1.len()
        invariant
            str1.len() == str1.len(),
            forall |k: int| 0 <= k < str1.len() ==> str1[k] == str1[k],
            result.len() <= str1.len(),
            index <= result.len(), // Modified by AI
        decreases str1.len() - index,
    {
        if ((str1[index] == 32) || (str1[index] == 44) || (str1[index] == 46)) {
            result.push(58);
        } else {
            result.push(str1[index]);
        }
        index += 1;
        
        proof {
            result_len_invariant(str1.len(), result.len());
        }
    }
    proof {
        assert(forall|k: int| 
            0 <= k < result@.len() ==> #[trigger] result[k] == (if is_space_comma_dot_spec(str1[k]) {
                58
            } else {
                str1[k]
            })
        ); // Added by AI
    }
    result
}

}

// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2
// Safe: True