use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn all_sequence_equal_length(seq: &Vec<Vec<i32>>) -> (result: bool)
    requires
        seq.len() > 0,
    ensures
        result == (forall|i: int, j: int|
            (0 <= i < seq.len() && 0 <= j < seq.len()) ==> (#[trigger] seq[i].len()
                == #[trigger] seq[j].len())),
{
    let mut index = 1;
    while index < seq.len() 
    invariant
        seq.len() > 0,
        forall|i: int, j: int| 0 <= i < index && 0 <= j < index ==> seq[i].len() == seq[j].len(),
        forall|i: int| 0 <= i < seq.len() ==> seq[i].len() >= 0,
    decreases seq.len() - index, 
    {
        if ((&seq[index]).len() != (&seq[0]).len()) {
            return false;
        }
        index += 1;
    }
    proof {
        assert(forall|i: int, j: int|
            (0 <= i < seq.len() && 0 <= j < seq.len()) ==> seq[i].len() == seq[j].len());
    }
    true
}

} // verus!
// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True