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
            forall|k: int| 0 <= k < str.len() ==> str[k] == str[k]
        decreases str.len() - i
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
            forall|k: int| 0 <= k < index ==> str1[k] == str1[k],
            forall|k: int| 0 <= k < str2.len() ==> str2[k] == str2[k],
            output_str.len() <= index // Fixed by AI
        decreases str1.len() - index
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