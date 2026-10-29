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
        // Invariant added for all elements as `main` and `sub` are not changed in this loop
        forall |k: int| 0 <= k < i ==> main[idx + k] == sub[k],
    decreases
        sub.len() - i,
    {
        assert(forall |k: int| 0 <= k < i ==> main[idx + k] == sub[k]);
        if (main[idx + i] != sub[i]) {
            return false;
        }
        i += 1;
    }
    assert(forall |k: int| 0 <= k < sub.len() ==> main[idx + k] == sub[k]);
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
    decreases
        main.len() - index,
    {
        if (sub_array_at_index(&main, &sub, index)) {
            return true;
        }
        index += 1;
    }
    proof {
        assert(!exists|k: int, l: int| 0 <= k <= (main.len() - sub.len()) && l == k + sub.len() && (main@.subrange(k, l)) =~= sub@); // Added by AI
    }
    false
}

} // verus!

// Score: Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1
// Safe: True