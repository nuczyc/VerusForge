
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
            true,
            y <= 191, 
            7 * x <= 191, // invariant to ensure the product does not exceed 191
        decreases y
    {
        // Ensure the next value of x will not overflow
        assert(x < (u32::MAX) - 1);

        x = x + 1;

        // Assertion to prevent underflow for `191 - 7 * x`
    assert(191 >= 7 * x);  // Add proof computation
    assert(191 >= 7 * x);  // Add proof computation
    assert(191 >= 7 * x);  // Add proof computation
    assert(191 >= 7 * x);  // Add proof computation
    assert(191 >= 7 * x);  // Add proof computation
        assert(191 >= 7 * x);

        y = 191 - 7 * x;
    }
    (x, y)
}

} // verus!
fn main() {}
// Score: Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 3
// Safe: True