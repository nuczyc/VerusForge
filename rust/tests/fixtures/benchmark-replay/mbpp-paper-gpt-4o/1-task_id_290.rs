
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn max_length_list(seq: &Vec<Vec<i32>>) -> (max_list: &Vec<i32>)
    requires
        seq.len() > 0,
    ensures
        forall|k: int| 0 <= k < seq.len() ==> max_list.len() >= #[trigger] (seq[k]).len(),
        exists|k: int| 0 <= k < seq.len() && max_list@ =~= #[trigger] (seq[k]@),
{
    let mut max_list = &seq[0];
    let mut index = 1;

    while index < seq.len()
        invariant
            seq.len() > 0,
            0 <= index <= seq.len(),
            exists|k: int| 0 <= k < index && max_list@ =~= #[trigger] (seq[k]@),
            forall|k: int| 0 <= k < index ==> max_list.len() >= #[trigger] (seq[k]).len(),
        decreases seq.len() - index, 
    {
        if ((seq[index]).len() > max_list.len()) {
            max_list = &seq[index];
        }
        index += 1;
    }

    proof {
        assert(exists|k: int| 0 <= k < seq.len() && max_list@ =~= seq[k]@);
        assert(forall|k: int| 0 <= k < seq.len() ==> max_list.len() >= #[trigger] seq[k].len());
    }

    max_list
}

}

// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True