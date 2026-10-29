
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
        7 <= y,
    decreases y,
    {
        assert(7 * x <= 191); // Ensure no overflow occurs here
        x = x + 1;
    assert(191 >= 7 * x);  // Add proof computation
    assert(191 >= 7 * x);  // Add proof computation
    assert(191 >= 7 * x);  // Add proof computation
    assert(191 >= 7 * x);  // Add proof computation
    assert(191 >= 7 * x);  // Add proof computation
    assert(191 >= 7 * x);  // Add proof computation
        assert(191 >= 7 * x); // Ensure no underflow before assignment
        y = 191 - 7 * x;
    }
    (x, y)
}

} 

fn main() {}
// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 2
// Safe: True