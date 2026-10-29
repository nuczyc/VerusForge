
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn has_common_element(list1: &Vec<i32>, list2: &Vec<i32>) -> (result: bool)
    ensures
        result == (exists|i: int, j: int|
            0 <= i < list1.len() && 0 <= j < list2.len() && (list1[i] == list2[j])),
{
    let mut i = 0;
    while i < list1.len()
        invariant 0 <= i <= list1.len(),
        decreases list1.len() - i,
    {
        let mut j = 0;
        while j < list2.len()
            invariant 0 <= j <= list2.len(),
            decreases list2.len() - j,
        {
            if list1[i] == list2[j] {
                proof {
                    assert(exists|x: int, y: int| 0 <= x < list1.len() && 0 <= y < list2.len() && (list1[x] == list2[y]));
                }
                return true;
            }
            j += 1;
        }
        i += 1;
    }
    proof {
        assert(!exists|x: int, y: int| 0 <= x < list1.len() && 0 <= y < list2.len() && (list1[x] == list2[y])); // Added by AI
    }
    false
}

} // verus!

// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True