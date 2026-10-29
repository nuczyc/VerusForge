use vstd::prelude::*;

fn main() {}

verus! {

    /// Helper lemma to establish that any sequence length is non-negative.
    proof fn seq_len_is_non_negative(seq: &Vec<Vec<i32>>, idx: int)
        requires
            idx < seq.len(),
        ensures
            seq[idx].len() >= 0,
    {
        // Since indices are valid, the length is always non-negative
        assert(seq[idx].len() >= 0);
    }

    /// Helper lemma to prove that the invariant holds for all k < index + 1
    proof fn max_list_length_invariant(seq: &Vec<Vec<i32>>, max_list: &Vec<i32>, index: usize)
        requires
            seq.len() > 0,
            0 <= index < seq.len(),
            forall|k: int| 0 <= k < index ==> max_list.len() >= #[trigger] (seq[k]).len(),
        ensures
            forall|k: int| 0 <= k < index + 1 ==> max_list.len() >= #[trigger] (seq[k]).len(),
    {
        seq_len_is_non_negative(seq, index as int);
        assert(max_list.len() >= #[trigger] (seq[( index ) as int]).len());
    }

    /// Extend the invariant for while loop ensuring
    /// max_list length property and existence condition for max_list
    proof fn max_list_length_exists(seq: &Vec<Vec<i32>>, max_list: &Vec<i32>, index: usize)
        requires
            seq.len() > 0,
            0 <= index < seq.len(),
            forall|k: int| 0 <= k < index ==> max_list.len() >= #[trigger] (seq[k]).len(),
            exists|m: int| 0 <= m < index && max_list@ =~= #[trigger] (seq[m]@),
        ensures
            forall|k: int| 0 <= k < index + 1 ==> max_list.len() >= #[trigger] (seq[k]).len(),
            exists|m: int| 0 <= m < index + 1 && max_list@ =~= #[trigger] (seq[m]@),
    {
        seq_len_is_non_negative(seq, index as int);
        if max_list.len() >= #[trigger] seq[( index ) as int].len() {
            assert(exists|m: int| 0 <= m < index + 1 && max_list@ =~= #[trigger] seq[m]@) by {
                assert(exists|m: int| 0 <= m < index && max_list@ =~= #[trigger] seq[m]@);
            }
        } else {
            assert(max_list.len() < #[trigger] seq[( index ) as int].len());
            assert(max_list@ =~= #[trigger] seq[( index ) as int]@);
            assert(exists|m: int| 0 <= m < index + 1 && max_list@ =~= #[trigger] seq[m]@);
        }
    }

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
                seq.len() == seq.len(),
                max_list.len() == max_list.len(),
                forall|k: int| 0 <= k < index ==> max_list.len() >= #[trigger] (seq[k]).len(),
                exists|k: int| 0 <= k < index && max_list@ =~= #[trigger] (seq[k]@),
            decreases
                seq.len() - index,
        {
            assert(forall|k: int| 0 <= k < index ==> max_list.len() >= #[trigger] (seq[k]).len()) by {
                max_list_length_invariant(seq, max_list, ( index - 1 ) as usize);
            };

            if ((seq[index]).len() > max_list.len()) {
                max_list = &seq[index];
            }
            
            assert(forall|k: int| 0 <= k < index + 1 ==> max_list.len() >= #[trigger] (seq[k]).len()) by {
                max_list_length_exists(seq, max_list, index);
            };

            index += 1;
        }
        proof {
            assert(exists|k: int| 0 <= k < seq.len() && max_list@ =~= (seq[k]@));
        }
        max_list
    }

} // verus!


// Score: Compilation Error: False, Verified: 1, Errors: 4, Verus Errors: 4
// Safe: True