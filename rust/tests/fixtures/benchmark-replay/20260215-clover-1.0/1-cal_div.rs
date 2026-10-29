
use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]

fn cal_div() -> (r: (u32, u32))
    ensures
        r.0 == 27,
        r.1 == 2,
{
    let mut x: u32 = 0;
    let mut y: u32 = 191;
    while 7 <= y
    invariant
        // No array is read or written in this loop, so no invariant is needed for an array length.
        7 <= y <= 191, // Ensure y is within valid range
        x <= 27, // Ensure x does not cause overflow
    decreases(y) 
    {
    assert(x + 1 <= 27);  // Add proof computation
    assert(x + 1 <= 27);  // Add proof computation
    assert(x + 1 <= 27);  // Add proof computation
    assert(x + 1 <= 27);  // Add proof computation
    assert(x + 1 <= 27);  // Add proof computation
    assert(x + 1 <= 27);  // Add proof computation
    assert(x + 1 <= 27);  // Add proof computation
    assert(x + 1 <= 27);  // Add proof computation
        assert(x + 1 <= 27); // Assertion to prevent overflow

        x = x + 1;
        y = 191 - 7 * x;
    }
    (x, y)
}

} // verus!
fn main() {}
// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 2
// Safe: True