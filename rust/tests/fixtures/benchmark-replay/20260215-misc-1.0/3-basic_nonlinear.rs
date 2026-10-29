
use vstd::prelude::*;
fn main() {}

verus!{

#[verifier::loop_isolation(false)]
     
proof fn bound_check(x: u32, y: u32)
    requires
        x <= 0xffff,
        y <= 0xffff,
    ensures
        x*y <= 0x100000000,
{
    // By the requirements, it holds that:
    // 0 <= x <= 0xffff and 0 <= y <= 0xffff.
    // Therefore, the maximum value of x * y is (0xffff * 0xffff), which is less than 0x100000000,
    // because:
    // 0xffff * 0xffff = 0xfffe0001, which is 4294836225 in decimal, and indeed less than 4294967296.

    // You can add assertions or further reasoning here if desired, but the above logic shows why
    // the multiplication x * y will always be within the required bound.
    assert(x <= 0xffff);
    assert(y <= 0xffff);
    assert(x * y <= 0xffff * 0xffff);  // Add proof computation
    assert(x * y <= 0xffff * 0xffff);  // Add proof computation
    assert(x * y <= 0xffff * 0xffff);  // Add proof computation
    assert(x * y <= 0xffff * 0xffff);  // Add proof computation
    assert(x * y <= 0xffff * 0xffff);  // Add proof computation
    assert(x * y <= 0xffff * 0xffff);  // Add proof computation
    assert(x * y <= 0xffff * 0xffff);  // Add proof computation
    assert(x * y <= 0xffff * 0xffff);  // Add proof computation
    assert(x * y <= 0xffff * 0xffff);  // Add proof computation
    assert(x * y <= 0xffff * 0xffff);  // Add proof computation
    assert(x * y <= 0xffff * 0xffff); // Since both x and y are bounded by 0xffff.
    assert(x * y <= 0x100000000);
}
}
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True