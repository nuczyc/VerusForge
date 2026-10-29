
use vstd::prelude::*;
fn main() {}

verus!{

proof fn within_max_bound(res: u64)
    ensures 
        res + 1 <= u64::MAX,
{
    assert(res < u64::MAX) by {
        assert(u64::MAX - res > 0);
    }
}

#[verifier::loop_isolation(false)]
fn choose_odd()
{
    let mut idx: u64 = 0;
    let mut res: u64 = 5;
    while (idx < 10)
    invariant(idx <= 10) // Corrected by AI
    decreases(10 - idx) // Added by AI
    {
        proof { within_max_bound(res); }
        assert(res + 1 <= u64::MAX);  // Check bound before updating `res`
        res = res + 1;
        idx = idx + 1;
    }
    idx = 0;
    while (idx < 10)
    invariant(idx <= 10) // Corrected by AI
    decreases(10 - idx) // Added by AI
    {
        proof { within_max_bound(res); }
        assert(res + 1 <= u64::MAX);  // Check bound before updating `res`
        res = res + 1;
        idx = idx + 1;
    }
    assert(0 <= res);  // Establish lower bound
    assert(0 <= res);  // Establish lower bound
    assert(res == 25);
}
}
// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 2
// Safe: True