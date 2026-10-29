
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
        invariant forall |k: int| 0 <= k < list1.len() ==> 0 <= i < list1.len(),
        decreases list1.len() - i
    {
        let mut j = 0;
        while j < list2.len() 
            invariant forall |k: int| 0 <= k < list2.len() ==> 0 <= j < list2.len(),
            decreases list2.len() - j
        {
            if list1[i] == list2[j] {
                return true;
            }
            j += 1;
        }
        i += 1;
    }
    false
}

}

// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True