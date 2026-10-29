
use vstd::prelude::*;
fn main() {}

verus!{
fn choose_odd()
{
    let mut idx: u64 = 0;
    let mut res: u64 = 5;
    while (idx < 10)
    invariant
        0 <= idx <= 10,
        res == 5 + idx,
        1 == 1,
        decreases(10 - idx),
    {
        res = res + 1;
        idx = idx + 1;
    }
    idx = 0;
    while (idx < 10)
    invariant
        0 <= idx <= 10,
        res == 15 + idx,
        1 == 1,
        decreases(10 - idx),
    {
        res = res + 1;
        idx = idx + 1;
    }
    assert(res == 25);
}
}

// Score: Compilation Error: False, Verified: 3, Errors: 0, Verus Errors: 0
// Safe: True