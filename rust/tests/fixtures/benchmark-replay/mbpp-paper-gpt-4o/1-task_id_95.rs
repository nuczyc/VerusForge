use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn smallest_list_length(list: &Vec<Vec<i32>>) -> (min: usize)
    requires
        list.len() > 0,
    ensures
        min >= 0,
        forall|i: int| 0 <= i < list.len() ==> min <= #[trigger] list[i].len(),
        exists|i: int| 0 <= i < list.len() && min == #[trigger] list[i].len(),
{
    let mut min = list[0].len();
    let mut index = 1;
    while index < list.len()
        invariant
            list.len() > 0,
            0 <= index <= list.len(),
            exists|i: int| 0 <= i < index && min == #[trigger] list[i].len(),
            forall|i: int| 0 <= i < index ==> min <= #[trigger] list[i].len(), // Added by AI
        decreases list.len() - index,
    {
        if (&list[index]).len() < min {
            min = (&list[index]).len();
        }
        index += 1;
    }
    proof {
        assert(forall|i: int| 0 <= i < list.len() ==> min <= #[trigger] list[i].len());
    } // Added by AI
    min
}

}

// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True