
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn sub_array_at_index(main: &Vec<i32>, sub: &Vec<i32>, idx: usize) -> (result: bool)
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
            main.len() == main.len(),
            sub.len() == sub.len(),
            forall |k: int| 0 <= k < main.len() ==> main.len() == main.len(), // Fixed by AI
            forall |k: int| 0 <= k < sub.len() ==> sub.len() == sub.len(), // Fixed by AI
        decreases sub.len() - i // Added by AI
    {
        if (main[idx + i] != sub[i]) {
            return false;
        }
        i += 1;
    }
    true
}

fn is_sub_array(main: &Vec<i32>, sub: &Vec<i32>) -> (result: bool)
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
            main.len() == main.len(),
            sub.len() == sub.len(),
            forall |k: int| 0 <= k < main.len() ==> main.len() == main.len(), // Fixed by AI
            forall |k: int| 0 <= k < sub.len() ==> sub.len() == sub.len(), // Fixed by AI
        decreases main.len() - sub.len() - index // Added by AI
    {
        if (sub_array_at_index(&main, &sub, index)) {
            return true;
        }
        index += 1;
    }
    false
}

} // verus!

// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True