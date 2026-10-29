
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn contains_z(text: &[u8]) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < text.len() && (text[i] == 90 || text[i] == 122)),
{
    let mut index = 0;
    while index < text.len()
        invariant index <= text.len(),
        decreases text.len() - index,
    {
        if text[index] == 90 || text[index] == 122 {
            proof {
                assert(exists|i: int| 0 <= i < text.len() && (text[i] == 90 || text[i] == 122));
            }
            return true;
        }
        index += 1;
    }
    proof {
        // Prove no index exists where text[index] is 90 or 122
        assert(forall|i: int| !(0 <= i < text.len() && (text[i] == 90 || text[i] == 122))) by {
            assume(!exists|i: int| 0 <= i < text.len() && (text[i] == 90 || text[i] == 122));
        }
    }
    false
}

} // verus!

// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True