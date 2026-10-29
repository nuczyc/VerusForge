
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

proof fn lemma_increase_within_bounds(index: int, main_len: int, sub_len: int)
    requires
        0 <= index <= main_len - sub_len,
    ensures
        0 <= index + 1 <= main_len - sub_len,
{
    assert(index + 1 <= main_len - sub_len); // index incremented is within range
}

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
            main.len() == main.len(),
            sub.len() == sub.len(),
            forall |k: int| 0 <= k < main.len() ==> main[k] == main@[k], // Array main is not modified in the loop
            0 <= idx <= (main.len() - sub.len()),
        decreases
            sub.len() - i,
    {
        if (main[idx + i] != sub[i]) {
            return false;
        }
        i += 1;
    }
    proof {
        assert(main@.subrange(idx as int, (idx + sub@.len())) =~= sub@); // Added by AI
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
            main.len() == main.len(),
            sub.len() == sub.len(),
            forall |k: int| 0 <= k < main.len() ==> main[k] == main@[k], // Array main is not modified in the loop
            0 <= index <= main.len() - sub.len(),
        decreases
            main.len() - sub.len() - index,
    {
        if (is_sub_list_at_index(&main, &sub, index)) {
            return true;
        }
        index += 1;
        proof {
            lemma_increase_within_bounds(index - 1, main.len() as int, sub.len() as int);
        }
    }
    false
}

}

// Score: Compilation Error: False, Verified: 3, Errors: 2, Verus Errors: 2
// Safe: True