use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

spec fn is_digit_spec(c: u8) -> bool {
    c >= 48 && c <= 57
}

fn is_digit(c: u8) -> (res: bool)
    ensures
        res == is_digit_spec(c),
{
    c >= 48 && c <= 57
}

fn is_integer(text: &[u8]) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < text.len() ==> (#[trigger] is_digit_spec(text[i]))),
{
    let mut index = 0;
    while index < text.len()
        invariant
            index <= text.len(),
            forall|j: int| 0 <= j < index ==> is_digit_spec(text[j]), // Added by AI
        decreases text.len() - index, // Added by AI
    {
        if (!is_digit(text[index])) {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
// Score: Compilation Error: False, Verified: 3, Errors: 0, Verus Errors: 0
// Safe: True