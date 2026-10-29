
use vstd::prelude::*;

fn main() {}
verus! {

#[verifier::loop_isolation(false)]

spec fn divides(factor: nat, candidate: nat) -> bool {
    candidate % factor == 0
}

spec fn is_prime(candidate: nat) -> bool {
    &&& 1 < candidate
    &&& forall|factor: nat| 1 < factor && factor < candidate ==> !divides(factor, candidate)
}

fn test_prime(candidate: u64) -> (result: bool)
    requires
        1 < candidate,
    ensures
        result == is_prime(candidate as nat),
{
    let mut factor: u64 = 2;
    while factor < candidate
        invariant
            1 < candidate,
        decreases
            (candidate - factor) as int, // Added by AI
    {
        proof {
    assert(0 <= factor);  // Establish lower bound
    assert(0 <= factor);  // Establish lower bound
    assert(0 <= factor);  // Establish lower bound
    assert(0 <= factor);  // Establish lower bound
    assert(0 <= factor);  // Establish lower bound
    assert(0 <= factor);  // Establish lower bound
    assert(0 <= factor);  // Establish lower bound
    assert(0 <= factor);  // Establish lower bound
            assert(factor != 0); // Added by AI
        }
        if candidate % factor == 0 {
            return false;
        }
        factor = factor + 1;
    }
    true
}

} // verus!
// Score: Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 3
// Safe: True