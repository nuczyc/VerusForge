
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn min_sublist(seq: &Vec<Vec<i32>>) -> (min_list: &Vec<i32>)
    requires
        seq.len() > 0,
    ensures
        forall|k: int| 0 <= k < seq.len() ==> min_list.len() <= #[trigger] (seq[k]).len(),
        exists|k: int| 0 <= k < seq.len() && min_list@ =~= #[trigger] (seq[k]@),
{
    let mut min_list = &seq[0];
    let mut index = 1;

    while index < seq.len()
        invariant
            seq.len() > 0,
            min_list.len() == seq[index - 1].len(),
            forall|k: int| 0 <= k < seq.len() ==> #[trigger] seq[k].len() >= min_list.len(), // Fixed trigger annotation
            index <= seq.len(),
        decreases seq.len() - index // Added by AI
    {
        if ((seq[index]).len() < min_list.len()) {
            min_list = &seq[index];
        }
        index += 1;
    }
    min_list
}

} // verus!

// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 2
// Safe: True