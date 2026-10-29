use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

spec fn is_digit(c: u8) -> bool {
    (c >= 48 && c <= 57)
}

spec fn count_digits_recursively(seq: Seq<u8>) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_digits_recursively(seq.drop_last()) + if is_digit(seq.last()) {
            1 as int
        } else {
            0 as int
        }
    }
}

fn count_digits(text: &[u8]) -> (count: usize)
    ensures
        0 <= count <= text.len(),
        count_digits_recursively(text@) == count,
{
    let mut count = 0;
    let mut index = 0;

    while index < text.len()
        invariant
            0 <= index <= text.len(),
            text.len() == text.len(),
            0 <= count <= index,
            forall |k:int| 0 <= k < index ==> if is_digit(text[k]) { 1 as int } else { 0 as int } + 0 <= count as int, // Added invariant to relate counted digits
            forall |k:int| 0 <= k < text.len() ==> text[k] == text[k], 
        decreases text.len() - index
    {
        if (text[index] >= 48 && text[index] <= 57) {
            assert(count < text.len());
            count += 1;
        }
        index += 1;
    }

    assert(count_digits_recursively(text@) == count as int); // Added assertion to ensure postcondition
    count
}

}

// Score: Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1
// Safe: True