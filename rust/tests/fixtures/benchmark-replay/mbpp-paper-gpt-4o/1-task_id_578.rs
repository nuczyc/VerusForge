use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn interleave(s1: &Vec<i32>, s2: &Vec<i32>, s3: &Vec<i32>) -> (res: Vec<i32>)
    requires
        s1@.len() == s2@.len() && s2@.len() == s3@.len(),
        0 <= (s1@.len() * 3) <= i32::MAX,
    ensures
        res@.len() == s1@.len() * 3,
        forall|i: int|
            0 <= i < s1@.len() ==> (res[3 * i] == s1[i] && res[3 * i + 1] == s2[i] && res[3 * i + 2]
                == s3[i]),
{
    let new_seq_len = s1.len() * 3;
    let mut output_seq = Vec::with_capacity(new_seq_len);
    let mut index = 0;

    while index < s1.len() 
        invariant 
            0 <= index <= s1.len(),
            output_seq.len() == 3 * index,
            forall |j: int| 0 <= j < index ==> (output_seq[3 * j] == s1[j] && output_seq[3 * j + 1] == s2[j] && output_seq[3 * j + 2] == s3[j]), // Added by AI
        decreases s1.len() - index,
    {
        output_seq.push(s1[index]);
        output_seq.push(s2[index]);
        output_seq.push(s3[index]);
        index += 1;
    }
    output_seq
}

} // verus!
// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True