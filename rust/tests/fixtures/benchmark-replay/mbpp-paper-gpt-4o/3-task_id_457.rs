
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

proof fn exist_min_list_in_prefix(seq: &Vec<Vec<i32>>, index: usize, min_list: &Vec<i32>)
    requires
        seq.len() > 0,
        1 <= index <= seq.len(),
        min_list.len() == #[trigger] (seq[index - 1]).len(),
        min_list@ =~= #[trigger] (seq[index - 1]@),
    ensures
        exists|k: int| 0 <= k < index && min_list@ =~= #[trigger] (seq[k]@),
{
    assert(exists|k: int| 0 <= k < index && min_list@ =~= #[trigger] (seq[k]@));
}

proof fn exists_min_list_initial(seq: &Vec<Vec<i32>>, min_list: &Vec<i32>)
    requires
        seq.len() > 0,
        min_list.len() == #[trigger] (seq[0]).len(),
        min_list@ =~= #[trigger] (seq[0]@),
    ensures
        exists|k: int| 0 <= k < 1 && min_list@ =~= #[trigger] (seq[k]@),
{
    assert(exists|k: int| 0 <= k < 1 && min_list@ =~= #[trigger] (seq[k]@));
}

fn min_sublist(seq: &Vec<Vec<i32>>) -> (min_list: &Vec<i32>)
    requires
        seq.len() > 0,
    ensures
        forall|k: int| 0 <= k < seq.len() ==> min_list.len() <= #[trigger] (seq[k]).len(),
        exists|k: int| 0 <= k < seq.len() && min_list@ =~= #[trigger] (seq[k]@),
{
    let mut min_list = &seq[0];
    let mut index = 1;

    proof {
        exists_min_list_initial(seq, min_list);
    }

    while index < seq.len()
        invariant
            seq.len() > 0,
            1 <= index <= seq.len(),
            exists|k: int| 0 <= k < index && min_list@ =~= #[trigger] (seq[k]@),
        decreases seq.len() - index
    {
        if ((seq[index]).len() < min_list.len()) {
            min_list = &seq[index];
        }
        proof {
            assert(min_list.len() == seq[index - 1].len());
            if (min_list.len() == seq[index - 1].len()) && (min_list@ =~= seq[index - 1]@) {
                exist_min_list_in_prefix(seq, index, min_list);
            }
        }
        index += 1;
    }
    min_list
}

} // verus!

// Score: Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 2
// Safe: True