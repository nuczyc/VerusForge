use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn extract_rear_chars(s: &Vec<Vec<u8>>) -> (result: Vec<u8>)
    requires
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i].len() > 0,
    ensures
        s.len() == result.len(),
        forall|i: int| 0 <= i < s.len() ==> result[i] == #[trigger] s[i][s[i].len() - 1],
{
    let mut rear_chars: Vec<u8> = Vec::with_capacity(s.len());
    let mut index = 0;
    while index < s.len() 
        invariant
            forall|k: int| 0 <= k < s.len() ==> #[trigger] s[k].len() > 0,
            rear_chars.len() <= s.len(),
            rear_chars.len() == index, 
            forall|i: int| 0 <= i < index ==> rear_chars[i] == #[trigger] s[i][s[i].len() - 1], // Added by AI
            s.len() == s.len()
        decreases s.len() - index 
    {
        let seq = &s[index];
        rear_chars.push(seq[seq.len() - 1]);
        index += 1;
    }
    rear_chars
}

} // verus!
// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True