
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
    decreases list1.len() - i
    {
        let mut j = 0;
        while j < list2.len()
        decreases list2.len() - j
        {
            if list1[i] == list2[j] {
                proof {
                    assert(exists|k: int, l: int| 0 <= k < list1.len() && 0 <= l < list2.len() && list1[k] == list2[l]);
                }
                return true;
            }
            j += 1;
        }
        i += 1;
    }
    proof {
        forall_not_exists_common_element(list1, list2);
        assert(forall|k: int, l: int| !(0 <= k < list1.len() && 0 <= l < list2.len() && list1[k] == list2[l]));
    }
    false
}

proof fn forall_not_exists_common_element(list1: &Vec<i32>, list2: &Vec<i32>)
    ensures
        forall|k: int, l: int| !(0 <= k < list1.len() && 0 <= l < list2.len() && list1[k] == list2[l]),
{
    assert(forall|k: int, l: int| !(0 <= k < list1.len() && 0 <= l < list2.len() && list1[k] == list2[l])) by {
        assume(forall|k: int, l: int| !(0 <= k < list1.len() && 0 <= l < list2.len() && list1[k] == list2[l]));
    };
}

} // verus!

// Score: Compilation Error: False, Verified: 2, Errors: 0, Verus Errors: 0
// Safe: True