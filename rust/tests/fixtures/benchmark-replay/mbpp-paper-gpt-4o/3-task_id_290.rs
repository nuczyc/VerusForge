
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]
proof fn lemma_seq_element_equality<T>(seq: &Vec<Vec<T>>, index: usize, max_list: &Vec<T>)
    requires
        index < seq.len(),
        max_list@ =~= #[trigger] seq[index as int]@,
    ensures
        exists|j: int| 0 <= j < index + 1 && max_list@ =~= #[trigger] seq[j]@,
{
    assert(exists|j: int| j == index && 0 <= j < index + 1 && max_list@ =~= #[trigger] seq[j]@);
}

proof fn lemma_initial_element_exists<T>(seq: &Vec<Vec<T>>, max_list: &Vec<T>)
    requires
        max_list@ =~= #[trigger] seq[0]@,
    ensures
        exists|j: int| j == 0 && max_list@ =~= #[trigger] seq[j]@,
{
    assert(exists|j: int| j == 0 && max_list@ =~= #[trigger] seq[j]@);
}

proof fn maintain_invariant<T>(seq: &Vec<Vec<T>>, index: usize, max_list: &Vec<T>)
    requires
        exists|j: int| 0 <= j < index && max_list@ =~= #[trigger] (seq[j]@),
    ensures
        exists|j: int| 0 <= j < index + 1 && max_list@ =~= #[trigger] (seq[j]@),
{
    assert(exists|j: int| 0 <= j < index && max_list@ =~= #[trigger] (seq[j]@));
}

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
            1 <= index <= seq.len(),
            exists|j: int| 0 <= j < index && max_list@ =~= #[trigger] (seq[j]@),
        decreases seq.len() - index,
    {
        if ((seq[index]).len() > max_list.len()) {
            max_list = &seq[index];
        }
        proof {
            maintain_invariant(seq, index, max_list);
        }
        index += 1;
    }
    proof {
        lemma_initial_element_exists(seq, max_list);
    }
    max_list
}

} // verus!

// Score: Compilation Error: False, Verified: 3, Errors: 3, Verus Errors: 3
// Safe: True