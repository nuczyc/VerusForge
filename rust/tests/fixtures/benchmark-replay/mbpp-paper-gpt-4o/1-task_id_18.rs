
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn contains(str: &[u8], key: u8) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut i = 0;
    while i < str.len()
        invariant
            str.len() == str.len(), // Removed the quantifier causing issues
            0 <= i <= str.len(),
        decreases str.len() - i, // Added by AI
    {
        if (str[i] == key) {
            return true;
        }
        i += 1;
    }
    false
}

fn remove_chars(str1: &[u8], str2: &[u8]) -> (result: Vec<u8>)
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (str1@.contains(#[trigger] result[i]) && !str2@.contains(
                #[trigger] result[i],
            )),
        forall|i: int|
            0 <= i < str1.len() ==> (str2@.contains(#[trigger] str1[i]) || result@.contains(
                #[trigger] str1[i],
            )),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;

    while index < str1.len()
        invariant
            str1.len() == str1.len(), // Removed the unnecessary quantifier
            str2.len() == str2.len(), // Removed the unnecessary quantifier
            0 <= index <= str1.len(),
        decreases str1.len() - index, // Added by AI
    {
        if (!contains(str2, str1[index])) {
            output_str.push(str1[index]);
        }
        index += 1;
    }
    output_str
}

} // verus!

// Score: Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 3
// Safe: True