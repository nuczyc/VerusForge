
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn is_sub_list_at_index(main: &Vec<i32>, sub: &Vec<i32>, idx: usize) -> (result: bool)
    requires
        sub.len() <= main.len(),
        0 <= idx <= (main.len() - sub.len()),
    ensures
        result == (main@.subrange(idx as int, (idx + sub@.len())) =~= sub@),
{
    let mut i = 0;
    while i < sub.len()
        invariant
            sub.len() <= main.len(),
            0 <= idx <= (main.len() - sub.len()),
            sub.len() == sub.len(),
            main.len() == main.len(),
            // main array is read in this loop, hence adding invariant for all elements
            forall |k: int| 0 <= k < main.len() ==> main[k] == main[k],
        decreases
            sub.len() - i,
    {
        if (main[idx + i] != sub[i]) {
            return false;
        }
        i += 1;
    }
    true
}

fn is_sub_list(main: &Vec<i32>, sub: &Vec<i32>) -> (result: bool)
    requires
        sub.len() <= main.len(),
    ensures
        result == (exists|k: int, l: int|
            0 <= k <= (main.len() - sub.len()) && l == k + sub.len() && (#[trigger] (main@.subrange(
                k,
                l,
            ))) =~= sub@),
{
    if sub.len() > main.len() {
        return false;
    }
    let mut index = 0;
    while index <= (main.len() - sub.len())
        invariant
            sub.len() <= main.len(),
            sub.len() == sub.len(),
            main.len() == main.len(),
            // main array is read in this loop, hence adding invariant for all elements
            forall |k: int| 0 <= k < main.len() ==> main[k] == main[k],
        decreases
            (main.len() - index - sub.len() + 1),
    {
        if (is_sub_list_at_index(&main, &sub, index)) {
            proof {
                assert(exists|k: int, l: int| 0 <= k <= (main.len() - sub.len()) && l == k + sub.len() && (main@.subrange(k, l)) =~= sub@);
            }
            return true;
        }
        index += 1;
    }
    proof {
        assert(!exists|k: int, l: int| 0 <= k <= (main.len() - sub.len()) && l == k + sub.len() && (main@.subrange(k, l)) =~= sub@);
    } // Added by AI
    false
}

} // verus!

// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2
// Safe: True