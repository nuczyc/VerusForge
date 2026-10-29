
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

spec fn is_space_comma_dot_spec(c: u8) -> bool {
    (c == 32) || (c == 44) || (c == 46)
}

proof fn lemma_replace_spec(str1: Seq<u8>, result: Seq<u8>)
    requires
        str1.len() == result.len(),
        forall|k: int|
            0 <= k < result.len() ==> #[trigger] result[k] == (if is_space_comma_dot_spec(str1[k]) {
                58
            } else {
                str1[k]
            }),
    ensures
        forall|k: int|
            0 <= k < str1.len() ==> #[trigger] result[k] == (if is_space_comma_dot_spec(str1[k]) {
                58
            } else {
                str1[k]
            }),
{
    // The proof follows directly from the requires clause being equivalent to the ensures clause.
}

proof fn lemma_result_len(str1: Seq<u8>, result: Vec<u8>)
    requires
        str1.len() == result.len(),
    ensures
        str1.len() == result@.len(),
{

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
    decreases (str1.len() - index)
    {
        if ((str1[index] == 32) || (str1[index] == 44) || (str1[index] == 46)) {
            result.push(58);
        } else {
            result.push(str1[index]);
        }
        index += 1;
    }
    proof {
        assert(str1.len() == result.len()); // Added by AI
        assert(forall|k: int|
            0 <= k < result.len() ==> #[trigger] result[k] == (if is_space_comma_dot_spec(str1[k]) {
                58
            } else {
                str1[k]
            })); // Added by AI
        lemma_replace_spec(str1@, result@);
        lemma_result_len(str1@, result);
        assert(str1@.len() == result@.len());
        assert(forall|k: int|
            0 <= k < result@.len() ==> #[trigger] result@[k] == (if is_space_comma_dot_spec(str1@[k]) {
                58
            } else {
                str1@[k]
            }));
    }
    result
}

}

// Score: Compilation Error: False, Verified: 3, Errors: 2, Verus Errors: 2
// Safe: True