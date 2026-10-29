
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

proof fn max_u64_ensures_no_overflow(count: u64, len: usize)
    requires
        count <= len as u64,
        len <= usize::MAX,
    ensures
        count < u64::MAX,
{
    assert(len < u64::MAX);
    assert(count < u64::MAX);
}

proof fn count_uppercase_preserve(count: u64, len: usize)
    requires
        count <= len as u64,
        len <= usize::MAX,
    ensures
        count + 1 <= len as u64,
{
    assert(count < len as u64);
    assert(count + 1 <= len as u64);
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
            0 <= index <= text.len(),
            count <= text.len() as u64,
            text.len() == text.len(),
            forall |k: int| 0 <= k < text.len() ==> text[k] == text[k],
        decreases text.len() - index,
    {
        if (text[index] >= 65 && text[index] <= 90) {
            proof {
                max_u64_ensures_no_overflow(count, text.len());
                count_uppercase_preserve(count, text.len());
            }
            count += 1;
        }
        index += 1;
        proof {
            assert(count <= text.len() as u64);
        }
    }
    count
}

} // verus!

// Score: Compilation Error: False, Verified: 2, Errors: 3, Verus Errors: 3
// Safe: True