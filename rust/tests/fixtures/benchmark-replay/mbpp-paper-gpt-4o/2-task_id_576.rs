
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
            main.len() == main.len(),
            sub.len() == sub.len(),
            forall |k: int| 0 <= k < main.len() ==> main@[k] == main@[k],
        decreases sub.len() - i
    {
        if (main[idx + i] != sub[i]) {
            return false;
        }
        i += 1;
    }
    true
}

proof fn lemma_no_underflow(main_len: nat, sub_len: nat)
    requires
        sub_len <= main_len,
    ensures
        main_len - sub_len >= 0,
{
    // Trivial proof because sub_len <= main_len implies main_len - sub_len is non-negative
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

    assert(main.len() - sub.len() >= 0) by {
        lemma_no_underflow(main.len() as nat, sub.len() as nat);
    };

    let mut index = 0;
    while index <= (main.len() - sub.len())
        invariant
            main.len() == main.len(),
            sub.len() == sub.len(),
            forall |k: int| 0 <= k < main.len() ==> main@[k] == main@[k],
            index <= (main.len() - sub.len()),
        decreases main.len() - sub.len() - index
    {
        if (sub_array_at_index(&main, &sub, index)) {
            return true;
        }
        index += 1;
        proof {
            if index > 0 {
                // New assertion only if index was incremented
                assert(index <= main.len() - sub.len()) by {
                    lemma_no_underflow(main.len() as nat, sub.len() as nat);
                };
            }
        }
    }
    false
}

}

// Score: Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 2
// Safe: True