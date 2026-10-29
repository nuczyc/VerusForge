
use vstd::prelude::*;
fn main() {}

verus!{

#[verifier::loop_isolation(false)]
fn choose_odd()
{
    let mut idx: u64 = 0;
    let mut res: u64 = 5;
    while (idx < 10)
    decreases(10 - idx)
    {
        assert(res + 1 <= u64::MAX);
        res = res + 1;
        idx = idx + 1;
    }
    idx = 0;
    while (idx < 10)
    decreases(10 - idx)
    {
        assert(res + 1 <= u64::MAX);
        res = res + 1;
        idx = idx + 1;
    }
    assert(0 <= res);  // Establish lower bound
    assert(0 <= res);  // Establish lower bound
    assert(0 <= res);  // Establish lower bound
    assert(0 <= res);  // Establish lower bound
    assert(0 <= res);  // Establish lower bound
    assert(0 <= res);  // Establish lower bound
    assert(0 <= res);  // Establish lower bound
    assert(0 <= res);  // Establish lower bound
    assert(res == 25);
}
}
// Score: Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 3
// Safe: True