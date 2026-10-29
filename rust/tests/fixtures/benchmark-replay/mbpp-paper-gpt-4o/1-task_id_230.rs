use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn replace_blanks_with_chars(str1: &[u8], ch: u8) -> (result: Vec<u8>)
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> result[i] == (if str1[i] == 32 {
                ch
            } else {
                str1[i]
            }),
{
    let mut out_str: Vec<u8> = Vec::with_capacity(str1.len());
    let mut index = 0;
    while index < str1.len()
        invariant
            forall|k: int| 0 <= k < str1.len() ==> str1[k] == str1[k], // unchanged because str1 is not modified in the loop
            out_str.len() == index,
            out_str.len() <= str1.len(),
            forall|k: int| 
                0 <= k < out_str.len() ==> out_str[k] == (if str1[k] == 32 { ch } else { str1[k] }), // Added by AI
        decreases str1.len() - index, 
    {
        if str1[index] == 32 {
            out_str.push(ch);
        } else {
            out_str.push(str1[index]);
        }
        index += 1;

        proof {
            assert(out_str.len() == index);
        } 
    }
    out_str
}

// Helper proof function to assert out_str is within bounds of str1
proof fn lemma_out_str_len_bound(out_str_len: usize, str1_len: usize, index: usize)
    requires index <= str1_len, out_str_len == index
    ensures out_str_len <= str1_len
{
    assert(out_str_len <= str1_len);
}

} // verus!

// Score: Compilation Error: False, Verified: 2, Errors: 0, Verus Errors: 0
// Safe: True