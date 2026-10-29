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
    invariant
        0 <= index <= text.len(),
        text.len() == text.len(),
        forall |k: int| 0 <= k < text.len() ==> (text[k] == text[k]), // No modification happens to the elements of the array `text` in the loop.
        !exists|i: int| 0 <= i < index && (text[i] == 90 || text[i] == 122),
    decreases text.len() - index
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
        assert(!exists|i: int| 0 <= i < text.len() && (text[i] == 90 || text[i] == 122));
    }
    false
}

} // verus!
// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True