
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

spec fn is_lower_case(c: u8) -> bool {
    c >= 97 && c <= 122
}

spec fn is_upper_case(c: u8) -> bool {
    c >= 65 && c <= 90
}

spec fn count_uppercase_recursively(seq: Seq<u8>) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_uppercase_recursively(seq.drop_last()) + if is_upper_case(seq.last()) {
            1 as int
        } else {
            0 as int
        }
    }
}

fn count_uppercase(text: &[u8]) -> (count: u64)
    ensures
        0 <= count <= text.len(),
        count_uppercase_recursively(text@) == count,
{
    let mut index = 0;
    let mut count = 0;

    while index < text.len()
        invariant
            // This invariant covers every element in the array text without modification within the loop
            forall |k: int| 0 <= k < text.len() ==> (0 <= #[trigger] text[k] <= 255),
            count <= index as u64, // Invariant to ensure count never exceeds index
            count as usize <= text.len(), // Ensures count can never exceed the length of text
        decreases text.len() - index,
    {
        if (text[index] >= 65 && text[index] <= 90) {
            assert(count < text.len() as u64); // Ensure there's room before incrementing
            count += 1;
        }
        index += 1;
    }
    count
}

} // verus!

// Score: Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1
// Safe: True