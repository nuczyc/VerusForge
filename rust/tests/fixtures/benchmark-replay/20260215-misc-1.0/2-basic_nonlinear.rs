
use vstd::prelude::*;
fn main() {}

verus!{

proof fn lemma_u32_mult_upper_bound(x: u32, y: u32) 
    requires
        x <= 0xffff,
        y <= 0xffff,
    ensures
        x as u64 * y as u64 <= 0xffff as u64 * 0xffff as u64,
{
    assert(x as u64 <= 0xffff as u64);
    assert(y as u64 <= 0xffff as u64);
    assert(x as u64 * y as u64 <= 0xffff as u64 * y as u64) by {
        assert(x <= 0xffff);
    };
    assert(x as u64 * y as u64 <= 0xffff as u64 * 0xffff as u64);
}

proof fn lemma_bound_ffff_y(y: u32)
    requires
        y <= 0xffff,
    ensures
        0xffff as u64 * y as u64 <= 0xffff as u64 * 0xffff as u64,
{
    assert(y as u64 <= 0xffff as u64);
    assert(0xffff as u64 * y as u64 <= 0xffff as u64 * 0xffff as u64);
}

proof fn bound_check(x: u32, y: u32)
    requires
        x <= 0xffff,
        y <= 0xffff,
    ensures
        x * y <= 0x100000000,
{
    lemma_u32_mult_upper_bound(x, y);
    lemma_bound_ffff_y(y);
    assert((x as u64 * y as u64) <= 0xffff as u64 * 0xffff as u64);
    assert(x * y <= 0x100000000);
}
}

// Score: Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1
// Safe: True