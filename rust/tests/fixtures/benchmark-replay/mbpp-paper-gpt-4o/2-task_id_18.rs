
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
    decreases str.len() - i
    {
        if (str[i] == key) {
            return true;
        }
        i += 1;
    }
    false
}

proof fn preserved_elements_in_output(str1: Seq<u8>, str2: Seq<u8>, output_str: Seq<u8>)
    requires
        forall|i: int| 0 <= i < str1.len() ==> (str2.contains(str1.index(i)) || output_str.contains(str1.index(i))),
        forall|i: int| 0 <= i < output_str.len() ==> (str1.contains(output_str.index(i)) && !str2.contains(output_str.index(i))),
    ensures
        forall|i: int| 0 <= i < str1.len() ==> (str2.contains(#[trigger] str1.index(i)) || output_str.contains(#[trigger] str1.index(i))),
{
    // No additional proof steps are needed here since the condition is directly checked.
}

proof fn ensure_output_str_conditions(str1: Seq<u8>, str2: Seq<u8>, output_str: Seq<u8>)
    ensures
        forall|i: int| 0 <= i < output_str.len() ==> (str1.contains(output_str.index(i)) && !str2.contains(output_str.index(i))),
{
    assert(forall|i: int| 0 <= i < output_str.len() ==> (str1.contains(output_str.index(i)) && !str2.contains(output_str.index(i))));
}

proof fn character_removal_valid(str1: Seq<u8>, str2: Seq<u8>, output_str: Seq<u8>)
    ensures
        forall|i: int| 0 <= i < str1.len() ==> (str2.contains(str1.index(i)) || output_str.contains(str1.index(i))),
{
    assert(forall|i: int| 0 <= i < str1.len() ==> (str2.contains(#[trigger] str1.index(i)) || output_str.contains(#[trigger] str1.index(i))));
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
    decreases str1.len() - index
    {
        if (!contains(str2, str1[index])) {
            output_str.push(str1[index]);
        }
        index += 1;
    }

    proof {
        ensure_output_str_conditions(str1@, str2@, output_str@);
        character_removal_valid(str1@, str2@, output_str@);
    }

    output_str
}

} // verus!

// Score: Compilation Error: False, Verified: 3, Errors: 3, Verus Errors: 3
// Safe: True