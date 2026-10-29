use vstd::prelude::*;
fn main() {}
verus! {
fn increment(x: u64) -> (result: u64)
    requires x < 100,
    ensures result == x + 1,
{
    proof {
        /* VERUSSEEK_PROOF */
    }
    x + 1
}
}
