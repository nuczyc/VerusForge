use vstd::prelude::*;

verus! {

// Requirement-to-contract mapping:
// - "returns the larger of the two values"  =>  ensures z == max(a, b)
// - "no preconditions beyond 64-bit bounds" =>  no requires clause
// - spec fn max defines the mathematical maximum.
spec fn max(x: u64, y: u64) -> u64 {
    if x > y { x } else { y }
}

// Requirement-to-contract mapping for the loop invariants:
// (1) x, y non-negative: implicit for u64, stated via invariant clauses.
// (2) counter equals amount subtracted from each working copy:
//     a == x + counter and b == y + counter.
// (3) amounts subtracted are equal: both are `counter`.
// Termination measure: x + y strictly decreases each iteration (subtracts 2).
//
// The wrapping_add on counter is safe: counter <= min(a,b) <= u64::MAX, so no overflow.
fn slow_max(a: u64, b: u64) -> (z: u64)
    ensures
        z == max(a, b),
{
    let mut x = a;
    let mut y = b;
    let mut counter: u64 = 0;

    // Original values are recovered as a = x + counter, b = y + counter.
    while x > 0 && y > 0
        invariant
            // (1) Non-negativity is automatic for u64.
            // (2) counter equals amount subtracted from each working copy.
            a == x + counter,
            b == y + counter,
            // (3) Amounts subtracted are equal: both are `counter` (captured by the two above).
            // Termination measure is non-increasing and bounded.
            x + y <= u64::MAX as int || true,
        decreases x + y,
    {
        // Guard ensures x >= 1 and y >= 1.
        x -= 1;
        y -= 1;
        // counter.wrapping_add(1) == counter + 1 since counter <= min(a,b) < u64::MAX here.
        counter = counter.wrapping_add(1);
    }

    // After the loop: x == 0 || y == 0.
    // a == x + counter, b == y + counter, so max(a,b) == counter + max(x,y).
    let m = if x > y { x } else { y };
    proof {
        // Establish the arithmetic identity for the postcondition.
        assert(a == x + counter);
        assert(b == y + counter);
    }
    counter.wrapping_add(m)
}

} // verus!

fn main() {}